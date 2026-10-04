import DifferentialGeometry.Topology.Ehresmann.ProperSubmersion
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import DifferentialGeometry.Topology.Manifold.ChartDisk.Construction

/-!
# Ambient transport of sublevel sets (FC34, face form on a closed carrier)

Let `M` be a compact boundaryless manifold and `g : M × ℝ → ℝ` smooth.  Suppose that, for every `τ ∈ [0,1]`, the
slice `g (·, τ)` is a submersion on the band `|g (·, τ) - c| < ε` (a positive quantitative transversality margin
for the face `{g = c}`).  Then there is a diffeomorphism `Ψ` of `M` with `g (Ψ p, 1) < c ↔ g (p, 0) < c` and
`g (Ψ p, 1) = c ↔ g (p, 0) = c` for every `p`; hence `Ψ` carries the sublevel domain and the level set at time `0`
onto those at time `1`.

Proof: reparametrize time by `Real.smoothTransition`; lift the field `∂_τ` through `(φ ∘ G, τ)`, where `φ` is a
smooth monotone profile which is the identity-like near `c` and constant outside the band, so that the lift is
tangent to the levels of `G` on the band.  The related flow (`exists_compactlySupported_relatedFlow_of_local`)
preserves `φ ∘ G` and moves `τ` by translation; `Ψ` is its time-one map on the slice `τ = 0`.
-/

set_option autoImplicit false

noncomputable section
open Set Function Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Analysis.ODE

theorem expNegInvGlue_lt_of_nonneg_of_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    expNegInvGlue a < expNegInvGlue b := by
  have hb : 0 < b := ha.trans_lt hab
  rcases ha.eq_or_lt with h | ha'
  · rw [← h, expNegInvGlue.zero]
    exact expNegInvGlue.pos_of_pos hb
  · simp only [expNegInvGlue, not_le.mpr ha', not_le.mpr hb, ite_false]
    exact Real.exp_lt_exp.mpr (neg_lt_neg ((inv_lt_inv₀ hb ha').mpr hab))

theorem smoothTransition_lt_half {x : ℝ} (hx : x < 1 / 2) : Real.smoothTransition x < 1 / 2 := by
  rcases le_or_gt x 0 with h0 | h0
  · rw [Real.smoothTransition.zero_of_nonpos h0]
    norm_num
  · have hlt := expNegInvGlue_lt_of_nonneg_of_lt h0.le (show x < 1 - x by linarith)
    rw [Real.smoothTransition, div_lt_iff₀ (Real.smoothTransition.pos_denom x)]
    linarith

theorem half_lt_smoothTransition {x : ℝ} (hx : 1 / 2 < x) : 1 / 2 < Real.smoothTransition x := by
  rcases le_or_gt 1 x with h1 | h1
  · rw [Real.smoothTransition.one_of_one_le h1]
    norm_num
  · have hlt := expNegInvGlue_lt_of_nonneg_of_lt (show (0 : ℝ) ≤ 1 - x by linarith)
      (show 1 - x < x by linarith)
    rw [Real.smoothTransition, lt_div_iff₀ (Real.smoothTransition.pos_denom x)]
    linarith

/-- Values of the band profile `s ↦ smoothTransition ((s - c)/ε + 1/2)` decide the side of `c`. -/
theorem bandProfile_side {c ε s₁ s₂ : ℝ} (hε : 0 < ε)
    (h : Real.smoothTransition ((s₁ - c) / ε + 1 / 2) =
      Real.smoothTransition ((s₂ - c) / ε + 1 / 2)) :
    (s₁ < c ↔ s₂ < c) ∧ (s₁ = c ↔ s₂ = c) := by
  have key : ∀ s : ℝ, (s < c → Real.smoothTransition ((s - c) / ε + 1 / 2) < 1 / 2) ∧
      (s = c → Real.smoothTransition ((s - c) / ε + 1 / 2) = 1 / 2) ∧
      (c < s → 1 / 2 < Real.smoothTransition ((s - c) / ε + 1 / 2)) := by
    intro s
    refine ⟨fun hs => smoothTransition_lt_half ?_, fun hs => ?_, fun hs => half_lt_smoothTransition ?_⟩
    · have : (s - c) / ε < 0 := div_neg_of_neg_of_pos (by linarith) hε
      linarith
    · rw [hs, sub_self, zero_div, zero_add]
      exact DifferentialGeometry.Topology.smoothTransition_half
    · have : 0 < (s - c) / ε := div_pos (by linarith) hε
      linarith
  rcases lt_trichotomy s₁ c with h1 | h1 | h1 <;> rcases lt_trichotomy s₂ c with h2 | h2 | h2
  · exact ⟨iff_of_true h1 h2, iff_of_false h1.ne h2.ne⟩
  · have := (key s₁).1 h1; rw [h, (key s₂).2.1 h2] at this; exact absurd this (lt_irrefl _)
  · have := (key s₁).1 h1; rw [h] at this; linarith [(key s₂).2.2 h2]
  · have := (key s₁).2.1 h1; rw [h] at this; linarith [(key s₂).1 h2]
  · exact ⟨iff_of_false h1.not_lt h2.not_lt, iff_of_true h1 h2⟩
  · have := (key s₁).2.1 h1; rw [h] at this; linarith [(key s₂).2.2 h2]
  · have := (key s₁).2.2 h1; rw [h] at this; linarith [(key s₂).1 h2]
  · have := (key s₁).2.2 h1; rw [h, (key s₂).2.1 h2] at this; exact absurd this (lt_irrefl _)
  · exact ⟨iff_of_false (lt_asymm h1) (lt_asymm h2), iff_of_false h1.ne' h2.ne'⟩

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]

theorem mfderiv_apply_fst_of_prodSpace {Fm : X → ℝ × ℝ} {y : X}
    (hFm : MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) Fm y) (v : TangentSpace I y) :
    (mfderiv I 𝓘(ℝ, ℝ × ℝ) Fm y v).1 = mfderiv I 𝓘(ℝ) (fun z => (Fm z).1) y v := by
  have hfst : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ) (Prod.fst : ℝ × ℝ → ℝ) (Fm y) :=
    ((contDiff_fst : ContDiff ℝ 1 (Prod.fst : ℝ × ℝ → ℝ)).contMDiff.contMDiffAt).mdifferentiableAt
      one_ne_zero
  have hc := mfderiv_comp y hfst hFm
  change _ = mfderiv I 𝓘(ℝ) (Prod.fst ∘ Fm) y v
  rw [hc, mfderiv_eq_fderiv, fderiv_fst]
  rfl

theorem mfderiv_apply_snd_of_prodSpace {Fm : X → ℝ × ℝ} {y : X}
    (hFm : MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) Fm y) (v : TangentSpace I y) :
    (mfderiv I 𝓘(ℝ, ℝ × ℝ) Fm y v).2 = mfderiv I 𝓘(ℝ) (fun z => (Fm z).2) y v := by
  have hsnd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ) (Prod.snd : ℝ × ℝ → ℝ) (Fm y) :=
    ((contDiff_snd : ContDiff ℝ 1 (Prod.snd : ℝ × ℝ → ℝ)).contMDiff.contMDiffAt).mdifferentiableAt
      one_ne_zero
  have hc := mfderiv_comp y hsnd hFm
  change _ = mfderiv I 𝓘(ℝ) (Prod.snd ∘ Fm) y v
  rw [hc, mfderiv_eq_fderiv, fderiv_snd]
  rfl

/-- The flow of the field `(s, τ) ↦ (0, α s * β τ)` translates `τ` where both bumps equal one. -/
theorem flow_eq_of_bump_eq_one
    (Z : (y : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) y)
    (hZ : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ).tangent ∞
      (fun y ↦ (⟨y, Z y⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))))
    (hc : IsCompact (tsupport Z)) {A B s τ₀ t : ℝ}
    (hone : ∀ r ∈ Ioo A B, Z (s, r) = ((0 : ℝ), (1 : ℝ)))
    (h₀ : τ₀ ∈ Ioo A B) (h₁ : τ₀ + t ∈ Ioo A B) :
    compactSupportFlowDiffeomorph Z hZ hc t (s, τ₀) = (s, τ₀ + t) := by
  let γ : ℝ → ℝ × ℝ := fun r ↦ (s, τ₀ + r)
  have hγ : IsMIntegralCurveOn γ Z (Ioo (A - τ₀) (B - τ₀)) := by
    intro r hr
    have hyr : τ₀ + r ∈ Ioo A B := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    change HasMFDerivWithinAt 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) γ (Ioo (A - τ₀) (B - τ₀)) r
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (s, τ₀ + r)))
    rw [hone _ hyr]
    exact (((hasDerivAt_const r s).prodMk ((hasDerivAt_id r).const_add τ₀)).hasDerivWithinAt
      ).hasFDerivWithinAt.hasMFDerivWithinAt
  let hcomplete := exists_globalIntegralCurve_of_compactSupport Z hZ hc
  have hzero : (0 : ℝ) ∈ Ioo (A - τ₀) (B - τ₀) := ⟨by linarith [h₀.1], by linarith [h₀.2]⟩
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hzero
    (hZ.of_le (by norm_num)) ((curveAt_integralCurve Z hcomplete (s, τ₀)).isMIntegralCurveOn _) hγ
    (by simpa only [γ, add_zero] using curveAt_zero Z hcomplete (s, τ₀))
  have hh := heq (show t ∈ Ioo (A - τ₀) (B - τ₀) from
    ⟨by linarith [h₁.1], by linarith [h₁.2]⟩)
  change curveAt Z hcomplete (s, τ₀) t = (s, τ₀ + t)
  exact hh

section Closed

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

/-- **FC34b (closed carrier, face form).** If every slice `g (·, τ)`, `τ ∈ [0,1]`, is a submersion on the band
`|g (·, τ) - c| < ε`, a diffeomorphism of `M` carries `{g (·, 0) < c}` and `{g (·, 0) = c}` onto
`{g (·, 1) < c}` and `{g (·, 1) = c}`. -/
theorem exists_diffeomorph_sublevel_of_band_transport
    (g : M × ℝ → ℝ) (hg : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ g) (c : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ p, |g (p, τ) - c| < ε →
      Surjective (mfderiv I 𝓘(ℝ) (fun z => g (z, τ)) p)) :
    ∃ Ψ : M ≃ₘ⟮I, I⟯ M, ∀ p,
      (g (Ψ p, 1) < c ↔ g (p, 0) < c) ∧ (g (Ψ p, 1) = c ↔ g (p, 0) = c) := by
  classical
  let σ : ℝ → ℝ := Real.smoothTransition
  have hσ : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ σ := Real.smoothTransition.contDiff.contMDiff
  have hσI : ∀ t, σ t ∈ Icc (0 : ℝ) 1 :=
    fun t => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  let G : M × ℝ → ℝ := fun x => g (x.1, σ x.2)
  have hG : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ G :=
    hg.comp (contMDiff_fst.prodMk (hσ.comp contMDiff_snd))
  let φ : ℝ → ℝ := fun s => σ ((s - c) / ε + 1 / 2)
  have hφ : ContDiff ℝ ∞ φ :=
    Real.smoothTransition.contDiff.comp
      (((contDiff_id.sub contDiff_const).div_const ε).add contDiff_const)
  have hφI : ∀ s, φ s ∈ Icc (0 : ℝ) 1 := fun s => hσI _
  -- the two maps to the plane
  let F : M × ℝ → ℝ × ℝ := fun x => (G x, x.2)
  let Ft : M × ℝ → ℝ × ℝ := fun x => (φ (G x), x.2)
  have hF : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ F := hG.prodMk_space contMDiff_snd
  have hFt : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ Ft :=
    (hφ.contMDiff.comp hG).prodMk_space contMDiff_snd
  -- bumps and fields
  let α : ContDiffBump (1 / 2 : ℝ) := ⟨3 / 2, 2, by norm_num, by norm_num⟩
  let β : ContDiffBump (1 / 2 : ℝ) := ⟨3 / 2, 2, by norm_num, by norm_num⟩
  have hα1 : ∀ s ∈ Icc (-1 : ℝ) 2, α s = 1 := by
    intro s hs
    apply α.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    change -(3 / 2 : ℝ) ≤ s - 1 / 2 ∧ s - 1 / 2 ≤ 3 / 2
    constructor <;> linarith [hs.1, hs.2]
  have hβ1 : ∀ s ∈ Icc (-1 : ℝ) 2, β s = 1 := hα1
  let Z : (y : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) y := fun y => ((0 : ℝ), α y.1 * β y.2)
  have hZ : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ).tangent ∞
      (fun y ↦ (⟨y, Z y⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr
      (contDiff_const.prodMk ((α.contDiff.comp contDiff_fst).mul (β.contDiff.comp contDiff_snd)))
  have hZc : IsCompact (tsupport Z) := by
    have hsub : tsupport Z ⊆ tsupport α ×ˢ tsupport β := by
      apply closure_minimal _ ((isClosed_tsupport _).prod (isClosed_tsupport _))
      intro y hy
      have hne : α y.1 * β y.2 ≠ 0 := by
        intro h0
        apply hy
        change ((0 : ℝ), α y.1 * β y.2) = (0 : ℝ × ℝ)
        rw [h0]
        rfl
      exact ⟨subset_tsupport _ (left_ne_zero_of_mul hne), subset_tsupport _ (right_ne_zero_of_mul hne)⟩
    exact (α.hasCompactSupport.isCompact.prod β.hasCompactSupport.isCompact).of_isClosed_subset
      (isClosed_tsupport _) hsub
  let Z' : (y : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) y := fun y => ((0 : ℝ), β y.2)
  have hZ' : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ).tangent ∞
      (fun y ↦ (⟨y, Z' y⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (contDiff_const.prodMk (β.contDiff.comp contDiff_snd))
  let Zβ : (y : ℝ) → TangentSpace 𝓘(ℝ) y := fun y => β y
  have hZβ : ContMDiff 𝓘(ℝ) 𝓘(ℝ).tangent ∞ (fun y ↦ (⟨y, Zβ y⟩ : TangentBundle 𝓘(ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr β.contDiff
  have hZFt : ∀ x, Z (Ft x) = ((0 : ℝ), β x.2) := by
    intro x
    change ((0 : ℝ), α (φ (G x)) * β x.2) = _
    rw [hα1 _ ⟨by linarith [(hφI (G x)).1], by linarith [(hφI (G x)).2]⟩, one_mul]
  have hFtd : ∀ x, MDifferentiableAt (I.prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) Ft x :=
    fun x => (hFt x).mdifferentiableAt (by simp)
  have hFd : ∀ x, MDifferentiableAt (I.prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) F x :=
    fun x => (hF x).mdifferentiableAt (by simp)
  -- local lifts of `Z` through `Ft`
  have Hloc : ∀ x₀ : M × ℝ, ∃ U ∈ 𝓝 x₀, ∃ Xloc : (x : M × ℝ) → TangentSpace (I.prod 𝓘(ℝ)) x,
      ContMDiffOn (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent ∞
          (fun x ↦ (⟨x, Xloc x⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))) U ∧
        (∀ x ∈ U, mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) Ft x (Xloc x) = Z (Ft x)) ∧
        (∀ x ∈ U, Z (Ft x) = 0 → Xloc x = 0) := by
    intro x₀
    by_cases hx₀ : |G x₀ - c| < ε
    · -- on the band: lift through `F = (G, τ)`, tangent to the levels of `G`
      have hsurj : Surjective (mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) F x₀) := by
        have hslice := hreg (σ x₀.2) (hσI x₀.2) x₀.1 hx₀
        have hι : MDifferentiableAt I (I.prod 𝓘(ℝ)) (fun z : M => (z, x₀.2)) x₀.1 :=
          ((contMDiff_id.prodMk contMDiff_const : ContMDiff I (I.prod 𝓘(ℝ)) ∞
            (fun z : M => (z, x₀.2))) x₀.1).mdifferentiableAt (by simp)
        have hGd : MDifferentiableAt (I.prod 𝓘(ℝ)) 𝓘(ℝ) G (x₀.1, x₀.2) :=
          (hG _).mdifferentiableAt (by simp)
        have hsndd : MDifferentiableAt (I.prod 𝓘(ℝ)) 𝓘(ℝ) (Prod.snd : M × ℝ → ℝ) (x₀.1, x₀.2) :=
          mdifferentiableAt_snd
        have hcG := mfderiv_comp x₀.1 hGd hι
        have hcS := mfderiv_comp x₀.1 hsndd hι
        have hconst : (Prod.snd ∘ fun z : M => (z, x₀.2)) = fun _ => x₀.2 := rfl
        rw [hconst, mfderiv_const, mfderiv_snd] at hcS
        let L : E →L[ℝ] E × ℝ := mfderiv I (I.prod 𝓘(ℝ)) (fun z : M => (z, x₀.2)) x₀.1
        let DG : E × ℝ →L[ℝ] ℝ := mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) G x₀
        rintro ⟨u, v⟩
        obtain ⟨w, hw⟩ := hslice (u - v * DG ((0 : E), (1 : ℝ)))
        have hw' : DG (L w) = u - v * DG ((0 : E), (1 : ℝ)) := by
          have h1 : mfderiv I 𝓘(ℝ) (G ∘ fun z : M => (z, x₀.2)) x₀.1 w =
              u - v * DG ((0 : E), (1 : ℝ)) := hw
          rw [hcG] at h1
          exact h1
        have hLw : (L w).2 = 0 := by
          have := congrArg (fun P : E →L[ℝ] ℝ => P w) hcS
          exact this.symm
        refine ⟨(v • ((0 : E), (1 : ℝ)) + L w : E × ℝ), ?_⟩
        apply Prod.ext
        · refine (mfderiv_apply_fst_of_prodSpace (hFd x₀) _).trans ?_
          change DG (v • ((0 : E), (1 : ℝ)) + L w) = u
          rw [map_add, map_smul, hw', smul_eq_mul]
          ring
        · refine (mfderiv_apply_snd_of_prodSpace (hFd x₀) _).trans ?_
          change mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) (Prod.snd : M × ℝ → ℝ) x₀
            (v • ((0 : E), (1 : ℝ)) + L w) = v
          rw [mfderiv_snd]
          change (v • ((0 : E), (1 : ℝ)) + L w).2 = v
          rw [Prod.snd_add, Prod.smul_snd, hLw, smul_eq_mul, mul_one, add_zero]
      obtain ⟨U, hU, Xl, hXs, hXrel, hXzero⟩ :=
        exists_local_smoothDerivativeLift_of_surjective F hF Z' hZ' x₀ hsurj
      refine ⟨U, hU, Xl, hXs, fun x hx => ?_, fun x hx hz => ?_⟩
      · have h := hXrel x hx
        have h1 : mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) G x (Xl x) = 0 := by
          have := congrArg Prod.fst h
          rw [mfderiv_apply_fst_of_prodSpace (hFd x)] at this
          exact this
        have h2 : mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) (Prod.snd : M × ℝ → ℝ) x (Xl x) = β x.2 := by
          have := congrArg Prod.snd h
          rw [mfderiv_apply_snd_of_prodSpace (hFd x)] at this
          exact this
        rw [hZFt]
        apply Prod.ext
        · rw [mfderiv_apply_fst_of_prodSpace (hFtd x)]
          have hφd : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) φ (G x) :=
            hφ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
          have hc := mfderiv_comp x hφd ((hG x).mdifferentiableAt (by simp))
          change mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) (φ ∘ G) x (Xl x) = 0
          rw [hc]
          change mfderiv 𝓘(ℝ) 𝓘(ℝ) φ (G x) (mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) G x (Xl x)) = 0
          rw [h1, map_zero]
        · rw [mfderiv_apply_snd_of_prodSpace (hFtd x)]
          exact h2
      · apply hXzero x hx
        rw [hZFt] at hz
        change ((0 : ℝ), β x.2) = 0 at hz
        change ((0 : ℝ), β (F x).2) = 0
        exact hz
    · -- off the band: `φ ∘ G` is locally constant, lift through `τ`
      have hsurjS : Surjective (mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) (Prod.snd : M × ℝ → ℝ) x₀) := by
        intro r
        refine ⟨(((0 : E), r) : E × ℝ), ?_⟩
        rw [mfderiv_snd]
        rfl
      obtain ⟨U, hU, Xl, hXs, hXrel, hXzero⟩ :=
        exists_local_smoothDerivativeLift_of_surjective (Prod.snd : M × ℝ → ℝ) contMDiff_snd Zβ hZβ
          x₀ hsurjS
      have hopen : IsOpen {x : M × ℝ | ε / 2 < |G x - c|} :=
        isOpen_lt continuous_const ((hG.continuous.sub continuous_const).abs)
      have hmem : x₀ ∈ {x : M × ℝ | ε / 2 < |G x - c|} := by
        change ε / 2 < |G x₀ - c|
        linarith [not_lt.mp hx₀]
      refine ⟨U ∩ {x | ε / 2 < |G x - c|}, inter_mem hU (hopen.mem_nhds hmem), Xl,
        hXs.mono inter_subset_left, fun x hx => ?_, fun x hx hz => ?_⟩
      · -- `φ ∘ G` is locally constant near `x`
        have hlc : (fun z => φ (G z)) =ᶠ[𝓝 x] fun _ => φ (G x) := by
          have hxb : ε / 2 < |G x - c| := hx.2
          rcases lt_abs.mp hxb with hpos | hneg
          · filter_upwards [hopen.mem_nhds hx.2,
              (isOpen_lt continuous_const (hG.continuous.sub continuous_const)).mem_nhds
                (show ε / 2 < G x - c from hpos)] with z _ hz
            have hz' : ε / 2 < G z - c := hz
            change Real.smoothTransition ((G z - c) / ε + 1 / 2) =
              Real.smoothTransition ((G x - c) / ε + 1 / 2)
            have h1 : 1 ≤ (G z - c) / ε + 1 / 2 := by
              have : 1 / 2 ≤ (G z - c) / ε := by rw [le_div_iff₀ hε]; linarith
              linarith
            have h2 : 1 ≤ (G x - c) / ε + 1 / 2 := by
              have : 1 / 2 ≤ (G x - c) / ε := by rw [le_div_iff₀ hε]; linarith
              linarith
            rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2]
          · filter_upwards [(isOpen_lt (hG.continuous.sub continuous_const) continuous_const).mem_nhds
                (show G x - c < -(ε / 2) by linarith)] with z hz
            have hz' : G z - c < -(ε / 2) := hz
            change Real.smoothTransition ((G z - c) / ε + 1 / 2) =
              Real.smoothTransition ((G x - c) / ε + 1 / 2)
            have h1 : (G z - c) / ε + 1 / 2 ≤ 0 := by
              have : (G z - c) / ε ≤ -(1 / 2) := by rw [div_le_iff₀ hε]; linarith
              linarith
            have h2 : (G x - c) / ε + 1 / 2 ≤ 0 := by
              have : (G x - c) / ε ≤ -(1 / 2) := by rw [div_le_iff₀ hε]; linarith
              linarith
            rw [Real.smoothTransition.zero_of_nonpos h1, Real.smoothTransition.zero_of_nonpos h2]
        rw [hZFt]
        apply Prod.ext
        · rw [mfderiv_apply_fst_of_prodSpace (hFtd x)]
          change mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) (fun z => φ (G z)) x (Xl x) = 0
          rw [hlc.mfderiv_eq, mfderiv_const]
          rfl
        · rw [mfderiv_apply_snd_of_prodSpace (hFtd x)]
          exact hXrel x hx.1
      · apply hXzero x hx.1
        rw [hZFt] at hz
        have := congrArg Prod.snd hz
        exact this
  -- properness of `Ft`
  have hproper : IsProperMap Ft := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hFt.continuous, fun K hK => ?_⟩
    apply (isCompact_univ.prod (hK.image continuous_snd)).of_isClosed_subset
      (hK.isClosed.preimage hFt.continuous)
    intro x hx
    exact ⟨mem_univ _, ⟨Ft x, hx, rfl⟩⟩
  obtain ⟨Xf, hXc, -, -, hflow⟩ := exists_compactlySupported_relatedFlow_of_local Ft hproper
    (hFt.of_le (by norm_num)) Z hZ hZc Hloc
  let D := compactSupportFlowDiffeomorph Xf Xf.contMDiff hXc
  let DZ := compactSupportFlowDiffeomorph Z hZ hZc
  have hone : ∀ s ∈ Icc (0 : ℝ) 1, ∀ r ∈ Ioo (-1 : ℝ) 2, Z (s, r) = ((0 : ℝ), (1 : ℝ)) := by
    intro s hs r hr
    change ((0 : ℝ), α s * β r) = _
    rw [hα1 s ⟨by linarith [hs.1], by linarith [hs.2]⟩, hβ1 r ⟨hr.1.le, hr.2.le⟩, one_mul]
  have hmove : ∀ (x : M × ℝ) (τ₀ t : ℝ), x.2 = τ₀ → τ₀ ∈ Ioo (-1 : ℝ) 2 → τ₀ + t ∈ Ioo (-1 : ℝ) 2 →
      Ft (D t x) = (φ (G x), τ₀ + t) := by
    intro x τ₀ t hx h₀ h₁
    rw [hflow t x]
    change DZ t (φ (G x), x.2) = _
    rw [hx]
    exact flow_eq_of_bump_eq_one Z hZ hZc (hone _ (hφI (G x))) h₀ h₁
  have hD1 : ∀ p : M, D 1 (p, 0) = ((D 1 (p, 0)).1, 1) := by
    intro p
    have := congrArg Prod.snd (hmove (p, 0) 0 1 rfl ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩)
    exact Prod.ext rfl (by simpa using this)
  have hDm1 : ∀ q : M, D (-1) (q, 1) = ((D (-1) (q, 1)).1, 0) := by
    intro q
    have := congrArg Prod.snd (hmove (q, 1) 1 (-1) rfl ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩)
    exact Prod.ext rfl (by simpa using this)
  have hsymm1 : (D 1).symm = D (-1) := compactSupportFlowDiffeomorph_symm Xf Xf.contMDiff hXc 1
  have hsymmm1 : (D (-1)).symm = D 1 := by
    rw [compactSupportFlowDiffeomorph_symm Xf Xf.contMDiff hXc (-1), neg_neg]
  let Ψ : M → M := fun p => (D 1 (p, 0)).1
  let Ψi : M → M := fun q => (D (-1) (q, 1)).1
  have hleft : LeftInverse Ψi Ψ := by
    intro p
    change (D (-1) ((D 1 (p, 0)).1, 1)).1 = p
    rw [← hD1 p, ← hsymm1, Diffeomorph.symm_apply_apply]
  have hright : RightInverse Ψi Ψ := by
    intro q
    change (D 1 ((D (-1) (q, 1)).1, 0)).1 = q
    rw [← hDm1 q, ← hsymmm1, Diffeomorph.symm_apply_apply]
  have hΨs : ContMDiff I I ∞ Ψ :=
    contMDiff_fst.comp ((D 1).contMDiff.comp (contMDiff_id.prodMk contMDiff_const))
  have hΨis : ContMDiff I I ∞ Ψi :=
    contMDiff_fst.comp ((D (-1)).contMDiff.comp (contMDiff_id.prodMk contMDiff_const))
  refine ⟨{ toEquiv := ⟨Ψ, Ψi, hleft, hright⟩, contMDiff_toFun := hΨs, contMDiff_invFun := hΨis },
    fun p => ?_⟩
  have hinv : φ (G (Ψ p, 1)) = φ (G (p, 0)) := by
    have := congrArg Prod.fst (hmove (p, 0) 0 1 rfl ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩)
    change φ (G (D 1 (p, 0))) = φ (G (p, 0)) at this
    rw [hD1 p] at this
    exact this
  have hG1 : G (Ψ p, 1) = g (Ψ p, 1) := by
    change g (Ψ p, σ 1) = _
    rw [show σ 1 = 1 from Real.smoothTransition.one]
  have hG0 : G (p, 0) = g (p, 0) := by
    change g (p, σ 0) = _
    rw [show σ 0 = 0 from Real.smoothTransition.zero]
  rw [hG1, hG0] at hinv
  exact bandProfile_side hε hinv

/-- Consumer (the ZSP02 sublevel-domain form): the diffeomorphism carries the closed sublevel domain and its
boundary level at time `0` onto those at time `1`. -/
theorem exists_diffeomorph_image_sublevel_of_band_transport
    (g : M × ℝ → ℝ) (hg : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ g) (c : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ p, |g (p, τ) - c| < ε →
      Surjective (mfderiv I 𝓘(ℝ) (fun z => g (z, τ)) p)) :
    ∃ Ψ : M ≃ₘ⟮I, I⟯ M, Ψ '' {p | g (p, 0) ≤ c} = {p | g (p, 1) ≤ c} ∧
      Ψ '' {p | g (p, 0) = c} = {p | g (p, 1) = c} := by
  obtain ⟨Ψ, hΨ⟩ := exists_diffeomorph_sublevel_of_band_transport g hg c hε hreg
  have hle : ∀ p, g (Ψ p, 1) ≤ c ↔ g (p, 0) ≤ c := fun p => by
    rw [le_iff_lt_or_eq, le_iff_lt_or_eq, (hΨ p).1, (hΨ p).2]
  refine ⟨Ψ, Set.ext fun q => ⟨?_, fun hq => ⟨Ψ.symm q, ?_, Ψ.apply_symm_apply q⟩⟩,
    Set.ext fun q => ⟨?_, fun hq => ⟨Ψ.symm q, ?_, Ψ.apply_symm_apply q⟩⟩⟩
  · rintro ⟨p, hp, rfl⟩
    exact (hle p).mpr hp
  · have := (hle (Ψ.symm q)).mp (by rw [Ψ.apply_symm_apply]; exact hq)
    exact this
  · rintro ⟨p, hp, rfl⟩
    exact (hΨ p).2.mpr hp
  · exact (hΨ (Ψ.symm q)).2.mp (by rw [Ψ.apply_symm_apply]; exact hq)

end Closed

end DifferentialGeometry.Topology.Ehresmann
