import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Matching the joint iterated derivative of two families with a common one-sided jet

For the parametrized half-line smooth-extension glue (`borel_halfLine_extend_param`) one must
know that two functions on the closed slab `Set.Ici 0 ×ˢ V` which are both `C∞` there and which
share their entire one-sided `t`-jet at every seam parameter `z ∈ V` have the *same* joint
iterated Fréchet derivative at every seam point `(0, z)`.

The natural reduction sets `D := Φ - ψ`. By linearity of `iteratedDerivWithin` over subtraction
the hypothesis becomes that *all* one-sided `t`-jets of `D` vanish on `V`:
`∀ i, ∀ w ∈ V, iteratedDerivWithin i (D · w) (Set.Ici 0) 0 = 0`, and the goal becomes
`iteratedFDerivWithin n D (Set.Ici 0 ×ˢ V) (0, z) = 0`. This `t`-jet–vanishing reduction is what
this file establishes (`iteratedFDerivWithin_prod_match` is then immediate from
`iteratedFDerivWithin_prod_match_zero_of_jet_vanish` by `iteratedFDerivWithin_sub_apply`).

## The deep step

The vanishing `iteratedFDerivWithin_prod_match_zero_of_jet_vanish` is the bivariate-Taylor /
mixed-partial heart of the half-line glue. It is proved by induction on `n`, strengthening the
statement to vanishing on the whole seam `{0} ×ˢ V`. The successor step factors the `(n+1)`-th
derivative through `iteratedFDerivWithin_succ_eq_comp_left`, reducing to the vanishing of the
Fréchet derivative of `iteratedFDerivWithin n D` at the seam point. As a continuous linear map on
`ℝ × E` this is `0` once it kills the two spanning directions:

* the seam-tangential direction `(0, e)`, where the `n`-th derivative is identically `0` along the
  seam by the induction hypothesis, so its directional derivative vanishes;
* the transverse direction `(1, 0)`, where the directional-derivative–commutation
  `fderivWithin_iteratedFDerivWithin_apply_eq` turns the directional derivative of
  `iteratedFDerivWithin n D` into `iteratedFDerivWithin n` of the transverse partial `∂ₜ D`. The
  transverse partial again has all one-sided `t`-jets vanishing on `V` (it is `∂ₜ^{i+1} D`), so the
  induction hypothesis applies to it.

The transverse-direction commutation `fderivWithin_iteratedFDerivWithin_apply_eq` is exactly the
restricted (single-slot) `C∞` permutation symmetry of `iteratedFDerivWithin`: it moves the new
transverse slot past the existing `n` slots. Mathlib provides only the second-order Clairaut
symmetry `ContDiffWithinAt.isSymmSndFDerivWithinAt` (valid at `C²`, hence `C∞`) and the full
permutation symmetry `ContDiffWithinAt.iteratedFDerivWithin_comp_perm` only under analyticity
(`ContDiffWithinAt 𝕜 ω`, strictly stronger than `C∞`). The required `C∞` single-slot move is
bootstrapped here directly from the second-order symmetry by an induction on `n` through the
*outer* derivative (`iteratedFDerivWithin_succ_eq_comp_left`), which keeps the codomain fixed: the
successor step reduces, via the induction hypothesis at every point and `fderivWithin_clm_apply`, to
the second-order symmetry of the `C²` map `iteratedFDerivWithin ℝ n f s`. The whole file is
sorry-free. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis

section DirectionalCommutation

/-- **Single-slot `C∞` commutation of a directional derivative with `iteratedFDerivWithin`.**
For a `C∞` function `f` on a set `s` of unique differentiability, every point of which is
accumulated from the interior (`s ⊆ closure (interior s)`), the Fréchet derivative of the `n`-th
iterated derivative in a fixed direction `u` equals the `n`-th iterated derivative of the
directional partial `y ↦ fderivWithin ℝ f s y u`:
`fderivWithin ℝ (iteratedFDerivWithin ℝ n f s) s x u = iteratedFDerivWithin ℝ n (∂_u f) s x`.

Evaluated on a tuple this is the cyclic permutation symmetry of `iteratedFDerivWithin (n+1)`
(moving the leading slot, `Fin.cons u m`, to the trailing slot, `Fin.snoc m u`). It bootstraps from
the second-order Clairaut symmetry `ContDiffWithinAt.isSymmSndFDerivWithinAt` by induction on `n`
through the *outer* derivative (`iteratedFDerivWithin_succ_eq_comp_left`), which keeps the codomain
`W` fixed, so the domain `G` and codomain `W` may live in arbitrary (independent) universes. The
successor step reduces, via the induction hypothesis at every point of `s` and
`fderivWithin_clm_apply`, to the second-order symmetry of `H := iteratedFDerivWithin ℝ n f s`
(which is `C²`, being an iterated derivative of a `C∞` function); that symmetry holds because
`x ∈ closure (interior s)`. -/
theorem fderivWithin_iteratedFDerivWithin_apply_eq {G W : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {s : Set G} (hs : UniqueDiffOn ℝ s) (hs' : s ⊆ closure (interior s))
    (n : ℕ) {f : G → W} (hf : ContDiffOn ℝ ∞ f s) (u : G) :
    ∀ x ∈ s, fderivWithin ℝ (iteratedFDerivWithin ℝ n f s) s x u
      = iteratedFDerivWithin ℝ n (fun y => fderivWithin ℝ f s y u) s x := by
  induction n with
  | zero =>
    -- `iteratedFDerivWithin 0 g s = (curryFin0).symm ∘ g`; the linear iso commutes with `fderivWithin`.
    intro x hx
    rw [iteratedFDerivWithin_zero_eq_comp,
      LinearIsometryEquiv.comp_fderivWithin _ (hs x hx)]
    ext m
    rw [ContinuousLinearMap.comp_apply, iteratedFDerivWithin_zero_apply]
    rfl
  | succ n IH =>
    intro x hx
    -- Abbreviate the `n`-th iterate `H`; it is `C²` within `s` (an iterate of a `C∞` map).
    set H := iteratedFDerivWithin ℝ n f s with hH_def
    -- The currying linear isometry peeled off by `iteratedFDerivWithin_succ_eq_comp_left`.
    set e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => G) W).symm with he_def
    -- LHS factors through the outer derivative of `H` in direction `u`.
    have hLHS : fderivWithin ℝ (iteratedFDerivWithin ℝ (n + 1) f s) s x u
        = e (fderivWithin ℝ (fderivWithin ℝ H s) s x u) := by
      rw [iteratedFDerivWithin_succ_eq_comp_left]
      rw [e.comp_fderivWithin (f := fderivWithin ℝ H s) (hs x hx)]
      rfl
    -- RHS, by the induction hypothesis at every point, is the outer derivative of `∂_u H`.
    have hIHeq : Set.EqOn (iteratedFDerivWithin ℝ n (fun y => fderivWithin ℝ f s y u) s)
        (fun y => fderivWithin ℝ H s y u) s := fun y hy => (IH y hy).symm
    have hRHS : iteratedFDerivWithin ℝ (n + 1) (fun y => fderivWithin ℝ f s y u) s x
        = e (fderivWithin ℝ (fun y => fderivWithin ℝ H s y u) s x) := by
      rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply,
        fderivWithin_congr hIHeq (hIHeq hx)]
    -- The two outer derivatives agree by the second-order Clairaut symmetry of `H`.
    rw [hLHS, hRHS]
    congr 1
    -- `fderivWithin (∂_u H) s x = (fderivWithin (fderivWithin H s) s x).flip u`.
    have hHC2 : ContDiffWithinAt ℝ 2 H s x := by
      refine (hf x hx).iteratedFDerivWithin_right hs ?_ hx
      have h2n : (2 : WithTop ℕ∞) + (n : WithTop ℕ∞) = ((2 + n : ℕ∞) : WithTop ℕ∞) := by norm_cast
      rw [h2n]; exact_mod_cast le_top
    have hn2 : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞) := le_of_eq minSmoothness_of_isRCLikeNormedField
    have hsymH : IsSymmSndFDerivWithinAt ℝ H s x :=
      hHC2.isSymmSndFDerivWithinAt hn2 hs (hs' hx) hx
    have hHdiff : DifferentiableWithinAt ℝ (fderivWithin ℝ H s) s x :=
      (hHC2.fderivWithin_right hs (m := 1) le_rfl hx).differentiableWithinAt (by simp)
    have hflip : fderivWithin ℝ (fun y => fderivWithin ℝ H s y u) s x
        = (fderivWithin ℝ (fderivWithin ℝ H s) s x).flip u := by
      rw [fderivWithin_clm_apply (hs x hx) hHdiff (differentiableWithinAt_const u),
        fderivWithin_const_apply, ContinuousLinearMap.comp_zero, zero_add]
    refine ContinuousLinearMap.ext (fun v => ?_)
    rw [hflip, ContinuousLinearMap.flip_apply]
    exact hsymH.eq u v

end DirectionalCommutation

section ProdMatch

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Vanishing form of the seam jet match.** If `D` is `C∞` on the closed slab `Ici 0 ×ˢ V`
(`V` open) and *every* one-sided `t`-jet of `D` vanishes at every seam parameter `w ∈ V`, then
the joint iterated Fréchet derivative of `D` vanishes at every seam point `(0, w)`.

Proved by induction on `n`, strengthened to vanishing on the whole seam `{0} ×ˢ V`. The successor
step uses `iteratedFDerivWithin_succ_eq_comp_left` to reduce to the Fréchet derivative of
`iteratedFDerivWithin n D` vanishing as a continuous linear map on `ℝ × E`; it is then killed on
the seam-tangential direction `(0, e)` by the induction hypothesis and on the transverse direction
`(1, 0)` by `fderivWithin_iteratedFDerivWithin_apply_eq` together with the induction hypothesis
applied to the transverse partial `∂ₜ D` (whose `t`-jets are the shifted `t`-jets of `D`, hence
also vanish). -/
theorem iteratedFDerivWithin_prod_match_zero_of_jet_vanish
    {D : ℝ × E → F} {V : Set E} (hV : IsOpen V)
    (hD : ContDiffOn ℝ ∞ D (Set.Ici (0:ℝ) ×ˢ V))
    (hjet : ∀ i : ℕ, ∀ w ∈ V,
      iteratedDerivWithin i (fun t => D (t, w)) (Set.Ici 0) 0 = 0)
    (n : ℕ) {z : E} (hz : z ∈ V) :
    iteratedFDerivWithin ℝ n D (Set.Ici (0:ℝ) ×ˢ V) (0, z) = 0 := by
  set S : Set (ℝ × E) := Set.Ici (0:ℝ) ×ˢ V with hS_def
  have hUD : UniqueDiffOn ℝ S := UniqueDiffOn.prod (uniqueDiffOn_Ici 0) hV.uniqueDiffOn
  -- Every point of the slab is accumulated from its interior (the open right half-slab).
  have hSclo : S ⊆ closure (interior S) := by
    have hsub : Set.Ioi (0:ℝ) ×ˢ V ⊆ interior S := by
      rw [hS_def, interior_prod_eq, interior_Ici, hV.interior_eq]
    refine fun p hp => closure_mono hsub ?_
    rw [hS_def] at hp
    rw [closure_prod_eq, closure_Ioi]
    exact ⟨hp.1, subset_closure hp.2⟩
  -- Strengthen to a statement universally quantified over the family and the seam point, so the
  -- successor step can recurse into the transverse partial `∂ₜ D`.
  clear_value S
  induction n generalizing D z with
  | zero =>
    -- `iteratedFDerivWithin 0 D S (0, z) = D (0, z) = 0` by the `i = 0` jet hypothesis.
    have h0 : D (0, z) = 0 := by
      have := hjet 0 z hz
      rwa [iteratedDerivWithin_zero] at this
    ext m
    rw [iteratedFDerivWithin_zero_apply, h0]
    simp
  | succ n IH =>
    -- It suffices that the Fréchet derivative of the `n`-th iterated derivative vanishes at (0,z).
    have hmem : ((0:ℝ), z) ∈ S := by rw [hS_def]; exact ⟨Set.self_mem_Ici, hz⟩
    rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply]
    have hsuff : fderivWithin ℝ (iteratedFDerivWithin ℝ n D S) S (0, z) = 0 := by
      -- A continuous linear map on `ℝ × E` vanishes once it kills `(1,0)` and every `(0,e)`.
      refine ContinuousLinearMap.ext (fun p => ?_)
      obtain ⟨t, e⟩ := p
      have hsplit : (t, e) = t • ((1:ℝ), (0:E)) + ((0:ℝ), e) := by
        simp [Prod.smul_mk, Prod.mk_add_mk]
      rw [show (0 : (ℝ × E) →L[ℝ] ((ℝ × E) [×n]→L[ℝ] F)) (t, e) = 0 from rfl, hsplit, map_add,
        map_smul]
      -- Transverse direction `(1,0)`: commute with `iteratedFDerivWithin`, then use IH on `∂ₜ D`.
      have htrans : fderivWithin ℝ (iteratedFDerivWithin ℝ n D S) S (0, z) ((1:ℝ), (0:E)) = 0 := by
        rw [fderivWithin_iteratedFDerivWithin_apply_eq hUD hSclo n hD ((1:ℝ), (0:E)) (0, z) hmem]
        -- `∂ₜ D` is `C∞` on `S`.
        have hDt : ContDiffOn ℝ ∞ (fun y => fderivWithin ℝ D S y ((1:ℝ), (0:E))) S := by
          have hfd : ContDiffOn ℝ ∞ (fderivWithin ℝ D S) S :=
            hD.fderivWithin hUD (by exact_mod_cast le_top)
          exact hfd.clm_apply contDiffOn_const
        -- Its one-sided `t`-jets are the shifted `t`-jets of `D`, hence vanish on `V`.
        have hjett : ∀ i : ℕ, ∀ w ∈ V,
            iteratedDerivWithin i (fun t => fderivWithin ℝ D S (t, w) ((1:ℝ), (0:E)))
              (Set.Ici 0) 0 = 0 := by
          intro i w hw
          -- On `Ici 0`, `t ↦ ∂ₜ D (t,w)` equals `derivWithin (D · w) (Ici 0)`.
          have hcongr : Set.EqOn
              (fun t => fderivWithin ℝ D S (t, w) ((1:ℝ), (0:E)))
              (derivWithin (fun t => D (t, w)) (Set.Ici 0)) (Set.Ici 0) := by
            intro t ht
            have hmaps : Set.MapsTo (fun r : ℝ => (r, w)) (Set.Ici 0) S :=
              fun r hr => by rw [hS_def]; exact ⟨hr, hw⟩
            have hpairc : HasDerivWithinAt (fun r : ℝ => (r, w)) ((1:ℝ), (0:E)) (Set.Ici 0) t :=
              (hasDerivWithinAt_id t (Set.Ici 0)).prodMk (hasDerivWithinAt_const t _ w)
            have hDfd : HasFDerivWithinAt D (fderivWithin ℝ D S (t, w)) S (t, w) :=
              ((hD (t, w) (hmaps ht)).differentiableWithinAt (by simp)).hasFDerivWithinAt
            have hcomp : HasDerivWithinAt (fun r : ℝ => D (r, w))
                (fderivWithin ℝ D S (t, w) ((1:ℝ), (0:E))) (Set.Ici 0) t :=
              (hDfd.comp_hasDerivWithinAt t hpairc hmaps)
            exact (hcomp.derivWithin (uniqueDiffOn_Ici 0 t ht)).symm
          rw [iteratedDerivWithin_congr hcongr Set.self_mem_Ici,
            ← iteratedDerivWithin_succ']
          exact hjet (i + 1) w hw
        exact IH hjett hz hDt
      -- Seam-tangential direction `(0,e)`: derivative of the `n`-th iterate along the seam is 0.
      have hseam : fderivWithin ℝ (iteratedFDerivWithin ℝ n D S) S (0, z) ((0:ℝ), e) = 0 := by
        -- Pull back along `ι : v ↦ (0, v)`; `iteratedFDerivWithin n D S ∘ ι = 0` on `V`.
        set ι : E → ℝ × E := fun v => (0, v) with hι_def
        set g : ℝ × E → (ℝ × E) [×n]→L[ℝ] F := iteratedFDerivWithin ℝ n D S with hg_def
        have hιmaps : Set.MapsTo ι V S := fun v hv => by
          rw [hS_def, hι_def]; exact ⟨Set.self_mem_Ici, hv⟩
        have hιfd : HasFDerivWithinAt ι (ContinuousLinearMap.inr ℝ ℝ E) V z := by
          simpa [hι_def] using (ContinuousLinearMap.inr ℝ ℝ E).hasFDerivWithinAt
        have hιdiff : DifferentiableWithinAt ℝ ι V z := hιfd.differentiableWithinAt
        have hgdiff : DifferentiableWithinAt ℝ g S (0, z) :=
          (hD.differentiableOn_iteratedFDerivWithin (by exact_mod_cast ENat.coe_lt_top n) hUD)
            (0, z) hmem
        -- The composite is identically `0` on `V` (the IH), so `fderivWithin (g ∘ ι) V z = 0`.
        have hcompzero : fderivWithin ℝ (g ∘ ι) V z = 0 := by
          have hEq : Set.EqOn (g ∘ ι) (fun _ => 0) V := by
            intro v hv
            simpa [hg_def, hι_def, Function.comp_apply] using IH hjet hv hD
          rw [fderivWithin_congr hEq (hEq hz), fderivWithin_const_apply]
        -- The chain rule expresses the same composite derivative through the seam direction.
        have hchain : fderivWithin ℝ (g ∘ ι) V z
            = (fderivWithin ℝ g S (0, z)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
          rw [fderivWithin_comp z hgdiff hιdiff hιmaps (hV.uniqueDiffOn z hz),
            hιfd.fderivWithin (hV.uniqueDiffOn z hz)]
        have happ := congrArg (fun L => L e) (hchain.symm.trans hcompzero)
        simpa [hg_def, ContinuousLinearMap.inr_apply] using happ
      rw [htrans, hseam, smul_zero, add_zero]
    rw [hsuff]
    simp only [LinearIsometryEquiv.map_zero]

/-- **Matching joint iterated derivatives from a common one-sided jet.** Two families `Φ, ψ` that
are both `C∞` on the closed slab `Ici 0 ×ˢ V` (`V` open) and share their entire one-sided `t`-jet
`i ↦ iteratedDerivWithin i (·, w)|_{Ici 0} 0` at every seam parameter `w ∈ V` have the same joint
iterated Fréchet derivative at every seam point `(0, z)`.

Reduces, via linearity of `iteratedFDerivWithin`/`iteratedDerivWithin` over subtraction, to the
vanishing statement `iteratedFDerivWithin_prod_match_zero_of_jet_vanish` for the difference
`D = Φ - ψ`. -/
theorem iteratedFDerivWithin_prod_match
    {Φ ψ : ℝ × E → F} {V : Set E} (hV : IsOpen V)
    (hΦ : ContDiffOn ℝ ∞ Φ (Set.Ici (0:ℝ) ×ˢ V)) (hψ : ContDiffOn ℝ ∞ ψ (Set.Ici (0:ℝ) ×ˢ V))
    (htjet : ∀ i : ℕ, Set.EqOn (fun w => iteratedDerivWithin i (fun t => Φ (t, w)) (Set.Ici 0) 0)
                               (fun w => iteratedDerivWithin i (fun t => ψ (t, w)) (Set.Ici 0) 0) V)
    (n : ℕ) {z : E} (hz : z ∈ V) :
    iteratedFDerivWithin ℝ n Φ (Set.Ici (0:ℝ) ×ˢ V) (0, z)
      = iteratedFDerivWithin ℝ n ψ (Set.Ici (0:ℝ) ×ˢ V) (0, z) := by
  -- Work with the difference `D = Φ - ψ`; the goal becomes `iteratedFDerivWithin n D · = 0`.
  set S : Set (ℝ × E) := Set.Ici (0:ℝ) ×ˢ V with hS_def
  have hUD : UniqueDiffOn ℝ S := UniqueDiffOn.prod (uniqueDiffOn_Ici 0) hV.uniqueDiffOn
  have hmem : ((0:ℝ), z) ∈ S := ⟨Set.self_mem_Ici, hz⟩
  have hΦn : ContDiffWithinAt ℝ n Φ S (0, z) :=
    (hΦ (0, z) hmem).of_le (by exact_mod_cast le_top)
  have hψn : ContDiffWithinAt ℝ n ψ S (0, z) :=
    (hψ (0, z) hmem).of_le (by exact_mod_cast le_top)
  -- `iteratedFDerivWithin n (Φ - ψ) = iteratedFDerivWithin n Φ - iteratedFDerivWithin n ψ`.
  have hsub : iteratedFDerivWithin ℝ n (Φ - ψ) S (0, z)
      = iteratedFDerivWithin ℝ n Φ S (0, z) - iteratedFDerivWithin ℝ n ψ S (0, z) :=
    iteratedFDerivWithin_sub_apply hΦn hψn hUD hmem
  -- The difference is `C∞` on `S`.
  have hD : ContDiffOn ℝ ∞ (Φ - ψ) S := hΦ.sub hψ
  -- All one-sided `t`-jets of the difference vanish on `V`, by linearity of `iteratedDerivWithin`.
  have hjet : ∀ i : ℕ, ∀ w ∈ V,
      iteratedDerivWithin i (fun t => (Φ - ψ) (t, w)) (Set.Ici 0) 0 = 0 := by
    intro i w hw
    have hΦw : ContDiffWithinAt ℝ i (fun t => Φ (t, w)) (Set.Ici 0) 0 := by
      have hcomp : ContDiffWithinAt ℝ ∞ (fun t : ℝ => Φ (t, w)) (Set.Ici 0) 0 := by
        have hmaps : Set.MapsTo (fun t : ℝ => (t, w)) (Set.Ici 0) S :=
          fun t ht => ⟨ht, hw⟩
        have hpair : ContDiffWithinAt ℝ ∞ (fun t : ℝ => (t, w)) (Set.Ici 0) 0 :=
          (contDiff_id.prodMk contDiff_const).contDiffWithinAt
        exact (hΦ (0, w) ⟨Set.self_mem_Ici, hw⟩).comp 0 hpair hmaps
      exact hcomp.of_le (by exact_mod_cast le_top)
    have hψw : ContDiffWithinAt ℝ i (fun t => ψ (t, w)) (Set.Ici 0) 0 := by
      have hcomp : ContDiffWithinAt ℝ ∞ (fun t : ℝ => ψ (t, w)) (Set.Ici 0) 0 := by
        have hmaps : Set.MapsTo (fun t : ℝ => (t, w)) (Set.Ici 0) S :=
          fun t ht => ⟨ht, hw⟩
        have hpair : ContDiffWithinAt ℝ ∞ (fun t : ℝ => (t, w)) (Set.Ici 0) 0 :=
          (contDiff_id.prodMk contDiff_const).contDiffWithinAt
        exact (hψ (0, w) ⟨Set.self_mem_Ici, hw⟩).comp 0 hpair hmaps
      exact hcomp.of_le (by exact_mod_cast le_top)
    have hsubt : (fun t => (Φ - ψ) (t, w)) = (fun t => Φ (t, w)) - (fun t => ψ (t, w)) := by
      funext t; simp [Pi.sub_apply]
    have htjetw : iteratedDerivWithin i (fun t => Φ (t, w)) (Set.Ici 0) 0
        = iteratedDerivWithin i (fun t => ψ (t, w)) (Set.Ici 0) 0 := htjet i hw
    rw [hsubt, iteratedDerivWithin_sub Set.self_mem_Ici (uniqueDiffOn_Ici 0) hΦw hψw,
      htjetw, sub_self]
  -- Apply the vanishing form and unwind.
  have hzero : iteratedFDerivWithin ℝ n (Φ - ψ) S (0, z) = 0 :=
    iteratedFDerivWithin_prod_match_zero_of_jet_vanish hV hD hjet n hz
  rw [hzero] at hsub
  exact sub_eq_zero.mp hsub.symm

end ProdMatch

end Analysis
end DifferentialGeometry
