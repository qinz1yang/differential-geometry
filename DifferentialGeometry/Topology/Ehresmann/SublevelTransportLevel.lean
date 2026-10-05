import DifferentialGeometry.Topology.Ehresmann.SublevelTransport
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# FC34b with transversality AT the level (the form ZSP02 applies)

Blueprint `master207B.tex`, FC34 (`lem:fibration-compact-transport`, B:6187–6206: a smooth family
`f_t` transverse to `X` and `∂X` for every `t ∈ [0,1]`, with the entire trace compact, transports
`f_0⁻¹ X` to `f_1⁻¹ X`) and its consumer ZSP02 (`thm:fibration-actual-zero-domains`, B:6374–6473:
"the entire family is transverse to .4 … Apply FC34's smooth ambient isotopy with target
half-line"). The tree's FC34b (`exists_diffeomorph_sublevel_of_band_transport`,
`SublevelTransport.lean`) asks for submersive slices on an open BAND `|g − c| < ε`. On a compact
carrier the level hypothesis already gives such a band:

* `eventually_surjective_slice`: surjectivity of the slice differential `d(g(·, τ))_p` is an open
  condition in `(p, τ)` (Mathlib's `ContMDiffAt.mfderiv` in tangent coordinates; a real covector is
  surjective iff nonzero).
* `exists_band_of_level_transversal`: if every slice `g(·, τ)`, `τ ∈ [0,1]`, is submersive at
  every point of the level `{g(·, τ) = c}`, there is `ε > 0` with submersive slices on the band
  (compactness of `M × [0,1]` minus an open neighbourhood of the level trace).
* `exists_diffeomorph_image_sublevel_of_level_transport` (FC34b, ZSP02's form): under the level
  hypothesis a diffeomorphism of `M` carries `{g(·,0) ≤ c}` and `{g(·,0) = c}` onto
  `{g(·,1) ≤ c}` and `{g(·,1) = c}`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Ehresmann

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
/-- A real covector on a tangent space is surjective as soon as it is nonzero. -/
theorem surjective_of_ne_zero_FC19 {p : M} {y : ℝ}
    (D : TangentSpace I p →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) y) (hD : D ≠ 0) : Surjective D := by
  obtain ⟨v, hv⟩ : ∃ v, D v ≠ 0 := by
    by_contra h
    push Not at h
    exact hD (ContinuousLinearMap.ext h)
  intro t
  let a : ℝ := t
  let b : ℝ := D v
  have hb : b ≠ 0 := hv
  refine ⟨(a / b) • v, ?_⟩
  rw [map_smul]
  change (a / b) * b = a
  field_simp

/-- **Openness of slice submersivity**: if the slice `g(·, τ₀)` has surjective differential at
`p₀`, so does `g(·, τ)` at `p` for every `(p, τ)` near `(p₀, τ₀)`. -/
theorem eventually_surjective_slice (g : M × ℝ → ℝ) (hg : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ g)
    (x₀ : M × ℝ) (h₀ : Surjective (mfderiv I 𝓘(ℝ) (fun z => g (z, x₀.2)) x₀.1)) :
    ∀ᶠ x in 𝓝 x₀, Surjective (mfderiv I 𝓘(ℝ) (fun z => g (z, x.2)) x.1) := by
  let f : M × ℝ → M → ℝ := fun x z => g (z, x.2)
  have hf : ContMDiffAt ((I.prod 𝓘(ℝ)).prod I) 𝓘(ℝ) ∞ (uncurry f) (x₀, x₀.1) := by
    have hs : ContMDiff ((I.prod 𝓘(ℝ)).prod I) (I.prod 𝓘(ℝ)) ∞
        (fun q : (M × ℝ) × M => (q.2, q.1.2)) :=
      contMDiff_snd.prodMk (contMDiff_snd.comp contMDiff_fst)
    exact (hg.comp hs).contMDiffAt
  have hpr : ContMDiffAt (I.prod 𝓘(ℝ)) I 0 (Prod.fst : M × ℝ → M) x₀ := contMDiffAt_fst
  have hφ := ContMDiffAt.mfderiv f Prod.fst hf hpr (by simp)
  set φ := inTangentCoordinates I 𝓘(ℝ) (Prod.fst : M × ℝ → M) (fun x => f x x.1)
    (fun x => mfderiv I 𝓘(ℝ) (f x) x.1) x₀ with hφdef
  have hcont : ContinuousAt φ x₀ := hφ.continuousAt
  have hsrc : ∀ᶠ x in 𝓝 x₀, x.1 ∈ (chartAt H x₀.1).source :=
    continuousAt_fst.preimage_mem_nhds ((chartAt H x₀.1).open_source.mem_nhds
      (mem_chart_source H x₀.1))
  have heq : ∀ x : M × ℝ, x.1 ∈ (chartAt H x₀.1).source →
      φ x = (mfderiv I 𝓘(ℝ) (f x) x.1).comp
        ((tangentBundleCore I M).coordChange (achart H x₀.1) (achart H x.1) x.1) := by
    intro x hx
    rw [hφdef, inTangentCoordinates_eq _ _ _ hx (by simp),
      tangentBundleCore_coordChange_model_space]
    rfl
  have hφ₀ : φ x₀ ≠ 0 := by
    rw [heq x₀ (mem_chart_source H x₀.1)]
    intro h0
    obtain ⟨v, hv⟩ := h₀ (1 : ℝ)
    have hS : (tangentBundleCore I M).coordChange (achart H x₀.1) (achart H x₀.1) x₀.1 v = v :=
      (tangentBundleCore I M).coordChange_self _ _ (mem_chart_source H x₀.1) v
    have h1 := congrArg (fun L : E →L[ℝ] ℝ => L v) h0
    change mfderiv I 𝓘(ℝ) (f x₀) x₀.1
      ((tangentBundleCore I M).coordChange (achart H x₀.1) (achart H x₀.1) x₀.1 v) = 0 at h1
    rw [hS] at h1
    have h2 : (1 : ℝ) = 0 := hv.symm.trans h1
    exact one_ne_zero h2
  have hne : ∀ᶠ x in 𝓝 x₀, φ x ≠ 0 := hcont.eventually_ne hφ₀
  filter_upwards [hne, hsrc] with x hx hxs
  apply surjective_of_ne_zero_FC19
  intro h0
  apply hx
  rw [heq x hxs]
  ext v
  have h1 : mfderiv I 𝓘(ℝ) (f x) x.1 = 0 := h0
  change mfderiv I 𝓘(ℝ) (f x) x.1
    ((tangentBundleCore I M).coordChange (achart H x₀.1) (achart H x.1) x.1 v) = 0
  rw [h1]
  rfl

section Closed

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- **Level transversality gives a band** on a compact carrier: if every slice `g(·, τ)`,
`τ ∈ [0,1]`, is submersive at every point of its level `c`, then for some `ε > 0` it is
submersive on the whole band `|g(·, τ) − c| < ε`. -/
theorem exists_band_of_level_transversal (g : M × ℝ → ℝ)
    (hg : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ g) (c : ℝ)
    (hlev : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ p, g (p, τ) = c →
      Surjective (mfderiv I 𝓘(ℝ) (fun z => g (z, τ)) p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ τ ∈ Icc (0 : ℝ) 1, ∀ p, |g (p, τ) - c| < ε →
      Surjective (mfderiv I 𝓘(ℝ) (fun z => g (z, τ)) p) := by
  classical
  let S : Set (M × ℝ) := {x | Surjective (mfderiv I 𝓘(ℝ) (fun z => g (z, x.2)) x.1)}
  have hSo : IsOpen (interior S) := isOpen_interior
  have hlevS : ∀ x : M × ℝ, x.2 ∈ Icc (0 : ℝ) 1 → g x = c → x ∈ interior S := by
    intro x hx hgx
    exact mem_interior_iff_mem_nhds.mpr (eventually_surjective_slice g hg x (hlev x.2 hx x.1 hgx))
  let K : Set (M × ℝ) := (univ ×ˢ Icc (0 : ℝ) 1) \ interior S
  have hK : IsCompact K :=
    (isCompact_univ.prod isCompact_Icc).diff hSo
  have hgc : Continuous fun x : M × ℝ => |g x - c| :=
    (hg.continuous.sub continuous_const).abs
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, fun τ hτ p _ => ?_⟩
    have hmem : (p, τ) ∉ K := by rw [hKe]; exact Set.notMem_empty _
    have : (p, τ) ∈ interior S := by
      by_contra hn
      exact hmem ⟨⟨mem_univ _, hτ⟩, hn⟩
    exact interior_subset this
  · obtain ⟨x₁, hx₁K, hmin⟩ := hK.exists_isMinOn hKne hgc.continuousOn
    have hpos : 0 < |g x₁ - c| := by
      rw [abs_pos, sub_ne_zero]
      intro hgx
      exact hx₁K.2 (hlevS x₁ hx₁K.1.2 hgx)
    refine ⟨|g x₁ - c|, hpos, fun τ hτ p hp => ?_⟩
    have : (p, τ) ∈ interior S := by
      by_contra hn
      have hmem : (p, τ) ∈ K := ⟨⟨mem_univ _, hτ⟩, hn⟩
      have h3 : |g x₁ - c| ≤ |g (p, τ) - c| := hmin hmem
      linarith
    exact interior_subset this

/-- **FC34b with level transversality (ZSP02's form).** If every slice `g(·, τ)`, `τ ∈ [0,1]`, is
submersive at its level `c`, a diffeomorphism of the compact carrier carries the closed sublevel
`{g(·,0) ≤ c}` and the level `{g(·,0) = c}` onto `{g(·,1) ≤ c}` and `{g(·,1) = c}`. -/
theorem exists_diffeomorph_image_sublevel_of_level_transport (g : M × ℝ → ℝ)
    (hg : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ g) (c : ℝ)
    (hlev : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ p, g (p, τ) = c →
      Surjective (mfderiv I 𝓘(ℝ) (fun z => g (z, τ)) p)) :
    ∃ Ψ : M ≃ₘ⟮I, I⟯ M, Ψ '' {p | g (p, 0) ≤ c} = {p | g (p, 1) ≤ c} ∧
      Ψ '' {p | g (p, 0) = c} = {p | g (p, 1) = c} := by
  obtain ⟨ε, hε, hband⟩ := exists_band_of_level_transversal g hg c hlev
  exact exists_diffeomorph_image_sublevel_of_band_transport g hg c hε hband

/-- **Consumer (ZSP02's affine family `(ZH)`).** For smooth `h₀, k : M → ℝ` on the compact carrier,
if every `h₀ + τk`, `τ ∈ [0,1]`, is submersive at its level `c`, a diffeomorphism carries the
closed sublevel and level of `h₀` onto those of `h₀ + k`. -/
theorem exists_diffeomorph_image_sublevel_of_affine_family {h₀ k : M → ℝ}
    (hh₀ : ContMDiff I 𝓘(ℝ) ∞ h₀) (hk : ContMDiff I 𝓘(ℝ) ∞ k) (c : ℝ)
    (hlev : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ p, h₀ p + τ * k p = c →
      Surjective (mfderiv I 𝓘(ℝ) (fun z => h₀ z + τ * k z) p)) :
    ∃ Ψ : M ≃ₘ⟮I, I⟯ M, Ψ '' {p | h₀ p ≤ c} = {p | h₀ p + k p ≤ c} ∧
      Ψ '' {p | h₀ p = c} = {p | h₀ p + k p = c} := by
  let G : M × ℝ → ℝ := fun x => h₀ x.1 + x.2 * k x.1
  have hG : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ G :=
    (hh₀.comp contMDiff_fst).add (contMDiff_snd.mul (hk.comp contMDiff_fst))
  obtain ⟨Ψ, h1, h2⟩ := exists_diffeomorph_image_sublevel_of_level_transport G hG c hlev
  refine ⟨Ψ, ?_, ?_⟩
  · convert h1 using 3 <;> simp [G]
  · convert h2 using 3 <;> simp [G]

end Closed

end DifferentialGeometry.Topology.Ehresmann
