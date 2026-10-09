import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Module.HahnBanach
import DifferentialGeometry.Topology.Manifold.OneManifold.GraphAtlasCoverBCF
import DifferentialGeometry.Topology.Manifold.OneManifold.HalfChart

/-!
# Graph atlases of one-dimensional bases from immersed embedded curves (lane B-BCF134)

The shared `K₃` kernel takes its base in graph-chart form (`GraphAtlas1_BCF`). A base described near
each point by a smooth embedding `σ : ℝ¹ → H` with injective differential onto a relatively open piece
(the boundary route's `SmoothProductChartAt_BIFc` base parametrizations, k = 1) has such an atlas:

* `exists_graphChart_of_immersion_BCF`: for a smooth `τ : ℝ → H` with `τ'(0) ≠ 0`, a continuous
  linear `ℓ` with `ℓ(τ'(0)) = 1` (Hahn–Banach) and the inverse function theorem for `ℓ ∘ τ` give a
  smooth `π` on an open `D ∋ ℓ(τ 0)` with `ℓ ∘ π = id` and `π(D) = τ(U)` for an open `U ∋ 0`;
* `exists_graphAtlas_of_immersions_BCF`: the atlas (indexed by the points of the base).
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **A graph chart along an immersed curve**: for a smooth `τ : ℝ → H` with `τ'(0) ≠ 0` there are a
continuous linear `ℓ`, a map `π` smooth on an open `D ∋ ℓ (τ 0)` with `ℓ ∘ π = id` on `D`, and an open
`U ∋ 0` with `π '' D = τ '' U`. -/
theorem exists_graphChart_of_immersion_BCF {τ : ℝ → H} (hτ : ContDiff ℝ ∞ τ)
    (hd : deriv τ 0 ≠ 0) :
    ∃ (ℓ : H →L[ℝ] ℝ) (π : ℝ → H) (D U : Set ℝ), IsOpen D ∧ IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ℓ (τ 0) ∈ D ∧ ContDiffOn ℝ ∞ π D ∧ (∀ b ∈ D, ℓ (π b) = b) ∧ π '' D = τ '' U := by
  obtain ⟨g, -, hg⟩ := exists_dual_vector ℝ (deriv τ 0) (norm_ne_zero_iff.mpr hd)
  set ℓ : H →L[ℝ] ℝ := ‖deriv τ 0‖⁻¹ • g with hℓ
  have hℓv : ℓ (deriv τ 0) = 1 := by
    rw [hℓ, smul_apply, hg]
    simp [norm_ne_zero_iff.mpr hd]
  have hτd : ∀ t, HasDerivAt τ (deriv τ t) t := fun t =>
    ((hτ.differentiable (by simp)) t).hasDerivAt
  have hhd : ∀ t, HasDerivAt (fun t => ℓ (τ t)) (ℓ (deriv τ t)) t := fun t =>
    ℓ.hasFDerivAt.comp_hasDerivAt t (hτd t)
  have hh : ContDiff ℝ ∞ (fun t => ℓ (τ t)) := ℓ.contDiff.comp hτ
  have hh0 : HasDerivAt (fun t => ℓ (τ t)) 1 0 := hℓv ▸ hhd 0
  set e := (hh.contDiffAt (x := 0)).toOpenPartialHomeomorph (fun t => ℓ (τ t))
    (hh0.hasFDerivAt_equiv one_ne_zero) (by simp) with he
  have he0 : (0 : ℝ) ∈ e.source := ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _
  have hecoe : ∀ t, e t = ℓ (τ t) := fun t => rfl
  set V : Set ℝ := {t | ℓ (deriv τ t) ≠ 0} with hV
  have hVo : IsOpen V := isOpen_ne_fun (ℓ.continuous.comp (hτ.continuous_deriv (by simp)))
    continuous_const
  have hV0 : (0 : ℝ) ∈ V := by
    change ℓ (deriv τ 0) ≠ 0
    rw [hℓv]
    exact one_ne_zero
  set e' := e.restrOpen V hVo with he'
  have he'0 : (0 : ℝ) ∈ e'.source := ⟨he0, hV0⟩
  refine ⟨ℓ, τ ∘ e'.symm, e'.target, e'.source, e'.open_target, e'.open_source, he'0,
    ?_, ?_, ?_, ?_⟩
  · have := e'.map_source he'0
    rwa [show e' 0 = ℓ (τ 0) from hecoe 0] at this
  · intro b hb
    have hsb : e'.symm b ∈ e'.source := e'.map_target hb
    have hsym : ContDiffAt ℝ ∞ e'.symm b :=
      e'.contDiffAt_symm_deriv hsb.2 hb (hhd (e'.symm b)) (hh.contDiffAt)
    exact (hτ.contDiffAt.comp b hsym).contDiffWithinAt
  · intro b hb
    change ℓ (τ (e'.symm b)) = b
    rw [← hecoe]
    exact e'.right_inv hb
  · rw [image_comp, e'.symm_image_target_eq_source]

/-- The embedding `t ↦ t e₀` of `ℝ` onto `ℝ¹`. -/
def lineToEuclid_BCF : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single 0 1)

theorem lineToEuclid_apply_zero_BCF (t : ℝ) : (lineToEuclid_BCF t) 0 = t := by
  simp [lineToEuclid_BCF]

theorem lineToEuclid_coord_BCF (x : EuclideanSpace ℝ (Fin 1)) : lineToEuclid_BCF (x 0) = x := by
  rw [Manifold.OneManifold.val_eq_single x]
  ext i
  fin_cases i
  simp [lineToEuclid_BCF]

/-- `lineToEuclid_BCF '' U = {x | x 0 ∈ U}`. -/
theorem image_lineToEuclid_BCF (U : Set ℝ) :
    lineToEuclid_BCF '' U = (fun x : EuclideanSpace ℝ (Fin 1) => x 0) ⁻¹' U := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    change (lineToEuclid_BCF t) 0 ∈ U
    rw [lineToEuclid_apply_zero_BCF]
    exact ht
  · intro hx
    exact ⟨x 0, hx, lineToEuclid_coord_BCF x⟩

/-- **A graph atlas from immersed embedded curves**: if every point `y` of `Bs` is `σ 0` for a smooth
embedding `σ : ℝ¹ → H` with injective differential onto a relatively open piece `Bs ∩ O`, then `Bs`
has a graph atlas (indexed by its points). -/
theorem exists_graphAtlas_of_immersions_BCF {Bs : Set H}
    (hσ : ∀ y ∈ Bs, ∃ (σ : EuclideanSpace ℝ (Fin 1) → H) (O : Set H), σ 0 = y ∧
      ContDiff ℝ ∞ σ ∧ IsEmbedding σ ∧ (∀ x, Injective (fderiv ℝ σ x)) ∧ IsOpen O ∧
      range σ = Bs ∩ O) :
    Nonempty (GraphAtlas1_BCF Bs Bs) := by
  have hloc : ∀ y : Bs, ∃ (ℓ : H →L[ℝ] ℝ) (π : ℝ → H) (D : Set ℝ), IsOpen D ∧
      ContDiffOn ℝ ∞ π D ∧ (∀ b ∈ D, ℓ (π b) = b) ∧
      (∃ G : Set H, IsOpen G ∧ G ∩ Bs = π '' D) ∧ (y : H) ∈ π '' D := by
    rintro ⟨y, hy⟩
    obtain ⟨σ, O, h0, hσs, hσe, hσi, hO, hr⟩ := hσ y hy
    set τ : ℝ → H := σ ∘ lineToEuclid_BCF with hτ
    have hτs : ContDiff ℝ ∞ τ := hσs.comp lineToEuclid_BCF.contDiff
    have hτd : deriv τ 0 ≠ 0 := by
      have hd : HasDerivAt τ (fderiv ℝ σ (lineToEuclid_BCF 0) (lineToEuclid_BCF 1)) 0 := by
        have h1 := ((hσs.differentiable (by simp)) (lineToEuclid_BCF 0)).hasFDerivAt
        have h2 := (lineToEuclid_BCF.hasFDerivAt (x := (0 : ℝ))).hasDerivAt
        simpa using h1.comp_hasDerivAt 0 h2
      rw [hd.deriv]
      intro h0'
      have hz := hσi _ (h0'.trans (map_zero _).symm)
      have := congrArg (fun x : EuclideanSpace ℝ (Fin 1) => x 0) hz
      simp [lineToEuclid_BCF] at this
    obtain ⟨ℓ, π, D, U, hD, hU, hU0, -, hπs, hπℓ, hπU⟩ := exists_graphChart_of_immersion_BCF hτs hτd
    have hUo : IsOpen ((fun x : EuclideanSpace ℝ (Fin 1) => x 0) ⁻¹' U) :=
      hU.preimage (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).continuous
    obtain ⟨G, hG, hGU⟩ := hσe.isInducing.isOpen_iff.mp hUo
    refine ⟨ℓ, π, D, hD, hπs, hπℓ, ⟨G ∩ O, hG.inter hO, ?_⟩, ?_⟩
    · rw [hπU, hτ, image_comp, image_lineToEuclid_BCF]
      ext z
      constructor
      · rintro ⟨⟨hzG, hzO⟩, hzB⟩
        obtain ⟨x, rfl⟩ : z ∈ range σ := hr ▸ ⟨hzB, hzO⟩
        exact ⟨x, by rw [← hGU]; exact hzG, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        have hxG : σ x ∈ G := by
          have : x ∈ σ ⁻¹' G := by rw [hGU]; exact hx
          exact this
        have hxr : σ x ∈ Bs ∩ O := hr ▸ mem_range_self x
        exact ⟨⟨hxG, hxr.2⟩, hxr.1⟩
    · rw [hπU]
      refine ⟨0, hU0, ?_⟩
      change σ (lineToEuclid_BCF 0) = y
      rw [map_zero, h0]
  choose ℓ π D hD hπs hπℓ hrel hmem using hloc
  exact ⟨{
    coord := ℓ
    param := π
    dom := D
    isOpen_dom := hD
    param_smooth := hπs
    coord_param := hπℓ
    piece_relOpen := hrel
    cover := by
      ext z
      constructor
      · intro hz
        exact mem_iUnion.mpr ⟨⟨z, hz⟩, hmem ⟨z, hz⟩⟩
      · intro hz
        obtain ⟨j, hj⟩ := mem_iUnion.mp hz
        obtain ⟨G, -, hGB⟩ := hrel j
        exact (hGB.symm ▸ hj : z ∈ G ∩ Bs).2 }⟩

end DifferentialGeometry.Topology
