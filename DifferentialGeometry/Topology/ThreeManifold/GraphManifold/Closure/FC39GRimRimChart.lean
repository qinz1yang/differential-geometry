import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSafeCircleTube
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1Standard
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# FC39 GROUP G, RIMBOX route B (sheet §3 K4, K7): kernels for the per-end rim charts

Lane FC39-G-RIMBOXc, dispositions D62-3 (d), (g). Four abstract pieces used by the binding
`FC39GRimRimChartBinding.lean`:

* `CircleBundle.isConnected_fibre_GRIM`, `CircleBundle.range_eq_fibre_GRIM` — the angular part of
  `target_full` (D62-3 (g)): a compact family of points of one fibre which is relatively open in it
  (= the fibre ∩ an open set) is the WHOLE fibre (the fibre is connected: the inverse
  trivialization of `{c} × S¹`);
* `rimReparam_GRIM` — the scaled reparametrization `(θ, x, y) ↦ (θ, lam x, endCoord b (τ y))`
  (ONE scale, D62-3 (d)): smooth, injective on a box where `τ' > 0`, with injective differential;
* `deriv_pos_of_nonneg_right_GRIM` — the inward sign: `q 0 = 0`, `q' 0 ≠ 0`, `q ≥ 0` to the right
  ⟹ `q' 0 > 0` (`edge_side` gives the sign, `descended_regular` the non-vanishing);
* `deriv_comp_ne_zero_of_coordinate_GRIM` — `(d ∘ γ)' ≠ 0` for a curve `γ` in a 1-manifold read
  by a coordinate `φ` with `φ ∘ γ` affine of nonzero slope and `dd ≠ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}}

/-! ## The angular part of `target_full` -/

/-- A whole fibre of the circle bundle is connected. -/
theorem CircleBundle.isConnected_fibre_GRIM (R : CircleBundle W) (c : R.Base) :
    IsConnected (R.fibre c) := by
  have hK : ({c} : Set R.Base) ⊆ R.neighborhood c :=
    singleton_subset_iff.mpr (R.mem_neighborhood c)
  have h := R.tube_eq_image_GSAFE c hK
  change R.tube {c} = _ at h
  have hfib : R.fibre c = R.tube {c} := rfl
  rw [hfib, h]
  have hpt : (Subtype.val ⁻¹' ({c} : Set R.Base) : Set (R.neighborhood c)) =
      {⟨c, R.mem_neighborhood c⟩} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro hx
      exact Subtype.ext hx
    · intro hx
      rw [hx]
  rw [hpt]
  exact (isConnected_singleton.prod isConnected_univ).image _
    (R.continuous_trivInv_GSAFE c).continuousOn

/-- **A compact family in one fibre which is relatively open in it is the whole fibre.** -/
theorem CircleBundle.range_eq_fibre_GRIM (R : CircleBundle W) {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [Nonempty S] (f : S → W.Carrier) (hf : Continuous f) {c : R.Base}
    (hfib : range f ⊆ R.fibre c) {T : Set W.Carrier} (hT : IsOpen T) (hfT : range f ⊆ T)
    (hTf : R.fibre c ∩ T ⊆ range f) : range f = R.fibre c := by
  refine Subset.antisymm hfib ?_
  have hA : IsClosed (range f) := (isCompact_range hf).isClosed
  have hpc := (R.isConnected_fibre_GRIM c).isPreconnected
  rw [isPreconnected_iff_subset_of_disjoint] at hpc
  have hcov : R.fibre c ⊆ T ∪ (range f)ᶜ := by
    intro x _
    by_cases h : x ∈ range f
    · exact Or.inl (hfT h)
    · exact Or.inr h
  have hdis : R.fibre c ∩ (T ∩ (range f)ᶜ) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and, not_not]
    intro hx hxT
    exact hTf ⟨hx, hxT⟩
  rcases hpc T (range f)ᶜ hT hA.isOpen_compl hcov hdis with h | h
  · exact fun x hx => hTf ⟨hx, h hx⟩
  · exfalso
    obtain ⟨s⟩ := ‹Nonempty S›
    exact h (hfib ⟨s, rfl⟩) ⟨s, rfl⟩

/-! ## The scaled reparametrization -/

/-- The scaled rim reparametrization `(θ, x, y) ↦ (θ, lam x, endCoord b (τ y))`. -/
def rimReparam_GRIM (lam : ℝ) (τ : ℝ → ℝ) (b : Bool) (p : Circle × (ℝ × ℝ)) :
    Circle × (ℝ × ℝ) :=
  (p.1, (lam * p.2.1, endCoord b (τ p.2.2)))

theorem contDiff_endCoord_comp_GRIM {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (b : Bool) :
    ContDiff ℝ ∞ (fun y => endCoord b (τ y)) := by
  cases b
  · exact hτ
  · exact contDiff_const.sub hτ

theorem hasDerivAt_endCoord_comp_GRIM {τ : ℝ → ℝ} {τ' y : ℝ} (hτ : HasDerivAt τ τ' y) (b : Bool) :
    HasDerivAt (fun y => endCoord b (τ y)) (if b then -τ' else τ') y := by
  cases b
  · exact hτ
  · have h := (hasDerivAt_const y (1 : ℝ)).sub hτ
    rw [zero_sub] at h
    exact h

theorem contMDiff_rimReparam_GRIM (lam : ℝ) {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (b : Bool) :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ∞ (rimReparam_GRIM lam τ b) := by
  have hA : ContDiff ℝ ∞ (fun v : ℝ × ℝ => (lam * v.1, endCoord b (τ v.2))) :=
    (contDiff_const.mul contDiff_fst).prodMk ((contDiff_endCoord_comp_GRIM hτ b).comp contDiff_snd)
  exact contMDiff_fst.prodMk (hA.contMDiff.comp contMDiff_snd)

/-- Injective on `S¹ × rimBox a` when `τ' > 0` on `[-a, a]`. -/
theorem rimReparam_injOn_GRIM {lam : ℝ} (hlam : lam ≠ 0) {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ)
    {a : ℝ} (hτd : ∀ y ∈ Icc (-a) a, 0 < deriv τ y) (b : Bool) :
    InjOn (rimReparam_GRIM lam τ b) {p | p.2 ∈ rimBox a} := by
  have hmono : StrictMonoOn τ (Icc (-a) a) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc (-a) a) hτ.continuous.continuousOn
      fun y hy => ?_
    rw [interior_Icc] at hy
    exact hτd y ⟨hy.1.le, hy.2.le⟩
  rintro p hp p' hp' h
  simp only [rimReparam_GRIM, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hx : p.2.1 = p'.2.1 := mul_left_cancel₀ hlam h2
  have hτy : τ p.2.2 = τ p'.2.2 := by
    cases b
    · exact h3
    · simp only [endCoord, ite_true] at h3
      linarith
  have hy : p.2.2 = p'.2.2 :=
    hmono.injOn ⟨by linarith [(abs_lt.mp hp.2).1], (abs_lt.mp hp.2).2.le⟩
      ⟨by linarith [(abs_lt.mp hp'.2).1], (abs_lt.mp hp'.2).2.le⟩ hτy
  exact Prod.ext h1 (Prod.ext hx hy)

/-- Injective differential where `τ' ≠ 0`. -/
theorem rimReparam_mfderiv_injective_GRIM {lam : ℝ} (hlam : lam ≠ 0) {τ : ℝ → ℝ}
    (hτ : ContDiff ℝ ∞ τ) (b : Bool) (p : Circle × (ℝ × ℝ)) (hτp : deriv τ p.2.2 ≠ 0) :
    Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ))
      (rimReparam_GRIM lam τ b) p) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set A : ℝ × ℝ → ℝ × ℝ := fun v => (lam * v.1, endCoord b (τ v.2)) with hAdef
  have hAc : ContDiff ℝ ∞ A :=
    (contDiff_const.mul contDiff_fst).prodMk ((contDiff_endCoord_comp_GRIM hτ b).comp contDiff_snd)
  have hprod : rimReparam_GRIM lam τ b = Prod.map id A := rfl
  have hidd : MDifferentiableAt (𝓡 1) (𝓡 1) (id : Circle → Circle) p.1 := mdifferentiableAt_id
  have hAd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) A p.2 :=
    (hAc.contMDiff p.2).mdifferentiableAt hn
  rw [hprod, mfderiv_prodMap hidd hAd, mfderiv_id]
  -- the derivative of `A`
  set d : ℝ := if b then -deriv τ p.2.2 else deriv τ p.2.2 with hd
  have hd0 : d ≠ 0 := by
    rw [hd]
    split_ifs
    · exact neg_ne_zero.mpr hτp
    · exact hτp
  have hτD : HasDerivAt τ (deriv τ p.2.2) p.2.2 :=
    ((hτ.differentiable (by simp)) p.2.2).hasDerivAt
  have hE := hasDerivAt_endCoord_comp_GRIM hτD b
  have hAF : HasFDerivAt A ((lam • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (d • ContinuousLinearMap.snd ℝ ℝ ℝ)) p.2 := by
    refine HasFDerivAt.prodMk ?_ ?_
    · exact (hasFDerivAt_fst.const_mul lam)
    · exact hE.comp_hasFDerivAt p.2 hasFDerivAt_snd
  have hAm : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) A p.2 = (lam • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (d • ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    rw [mfderiv_eq_fderiv, hAF.fderiv]
    rfl
  rw [hAm]
  intro w w' h
  have h' : ((w.1, (lam * w.2.1, d * w.2.2)) : EuclideanSpace ℝ (Fin 1) × (ℝ × ℝ)) =
      (w'.1, (lam * w'.2.1, d * w'.2.2)) := h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨h1, h2, h3⟩ := h'
  exact Prod.ext h1 (Prod.ext (mul_left_cancel₀ hlam h2) (mul_left_cancel₀ hd0 h3))

/-! ## The inward sign of the end profile -/

/-- `q 0 = 0`, `q' 0 ≠ 0` and `q ≥ 0` to the right of `0` give `q' 0 > 0`. -/
theorem deriv_pos_of_nonneg_right_GRIM {q : ℝ → ℝ} (hq : DifferentiableAt ℝ q 0) (hq0 : q 0 = 0)
    (hne : deriv q 0 ≠ 0) (hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 ≤ q s) : 0 < deriv q 0 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exfalso
    have ht := hq.hasDerivAt.tendsto_slope_zero_right
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (q (0 + t) - q 0) < 0 :=
      ht.eventually (gt_mem_nhds hlt)
    have hpos' : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, h1, h2, h3⟩ := (hev.and (hpos.and hpos')).exists
    rw [zero_add, hq0, sub_zero, smul_eq_mul] at h1
    have : 0 ≤ t⁻¹ * q t := mul_nonneg (inv_nonneg.mpr h3.le) h2
    linarith
  · exact hgt

/-- **The profile derivative does not vanish**: for a curve `γ` in a 1-manifold with `φ ∘ γ` affine of
nonzero slope near `s₀`, and `dd (γ s₀) ≠ 0`, `(d ∘ γ)' (s₀) ≠ 0`. -/
theorem deriv_comp_ne_zero_of_coordinate_GRIM {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) N] {γ : ℝ → N} {φ d : N → ℝ} {s₀ : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) γ s₀)
    (hφ : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) φ (γ s₀))
    (hdd : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) d (γ s₀)) {a c : ℝ} (ha : a ≠ 0)
    (hφγ : (fun s => φ (γ s)) =ᶠ[𝓝 s₀] fun s => a * s + c)
    (hd0 : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) d (γ s₀) ≠ 0) :
    deriv (fun s => d (γ s)) s₀ ≠ 0 := by
  set v := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ s₀ (1 : ℝ) with hv
  have haff : HasDerivAt (fun s : ℝ => a * s + c) a s₀ := by
    simpa using ((hasDerivAt_id s₀).const_mul a).add_const c
  have hφγd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => φ (γ s)) s₀ (1 : ℝ) = a := by
    rw [hφγ.mfderiv_eq, (hasMFDerivAt_iff_hasFDerivAt.mpr haff.hasFDerivAt).mfderiv]
    change ContinuousLinearMap.toSpanSingleton ℝ a (1 : ℝ) = a
    simp
  have hcomp : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => φ (γ s)) s₀ =
      (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ (γ s₀)).comp (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ s₀) :=
    mfderiv_comp s₀ hφ hγ
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => φ (γ s)) s₀ (1 : ℝ) =
        mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ (γ s₀) v := by
      rw [hcomp]
      rfl
    rw [hφγd, h0, map_zero] at h1
    exact ha h1
  set L := mfderiv (𝓡 1) 𝓘(ℝ, ℝ) d (γ s₀) with hL
  have hLv : L v ≠ 0 := by
    intro hLv
    apply hd0
    ext u
    have hrank : Module.finrank ℝ (TangentSpace (𝓡 1) (γ s₀)) = 1 := finrank_euclideanSpace_fin
    obtain ⟨k, hk⟩ := (finrank_eq_one_iff_of_nonzero' v hv0).mp hrank u
    rw [← hk, map_smul, hLv, smul_zero]
    rfl
  have hcompd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => d (γ s)) s₀ = L.comp
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ s₀) := mfderiv_comp s₀ hdd hγ
  intro h0
  apply hLv
  have h2 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => d (γ s)) s₀ (1 : ℝ) = L v := by
    rw [hcompd]
    rfl
  have hdiff : DifferentiableAt ℝ (fun s => d (γ s)) s₀ :=
    mdifferentiableAt_iff_differentiableAt.mp (hdd.comp s₀ hγ)
  rw [(hasMFDerivAt_iff_hasFDerivAt.mpr hdiff.hasDerivAt.hasFDerivAt).mfderiv] at h2
  change ContinuousLinearMap.toSpanSingleton ℝ (deriv (fun s => d (γ s)) s₀) (1 : ℝ) = L v at h2
  rw [h0] at h2
  have h3 : L v = (0 : ℝ) := by
    rw [← h2]
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_zero]
    rfl
  exact h3

end GC.GraphManifold.Assembly.FC39P0
