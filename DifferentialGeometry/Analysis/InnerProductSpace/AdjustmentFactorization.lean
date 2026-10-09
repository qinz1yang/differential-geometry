import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Postcomposition by an adjustment and retained projections (FC32, FC31 plateau clause)

The adjustment along a closed subspace `Q` of a real inner product space `H` with a map `P` taking values in `Q` is
`Ψ x = x + ψ x • (P (π_Q x) - π_Q x)`.

* FC32: postcomposition keeps fibres and kernels (inclusion only); `π_{Q⊥} ∘ Ψ = π_{Q⊥}`; for `Q₃ ≤ Q₂` and a cutoff
  depending only on the `Q₂`-coordinates, `π₂ ∘ Ψ₃ = Ψ₃₂ ∘ π₂` with `Ψ₃₂` the same adjustment applied to `π₂ x`.
* FC31 (plateau clause): where `ψ = 1`, `π_Q (Ψ y) = P (π_Q y)`; where `ψ ∘ f = 1` near `x`,
  `D (π_Q ∘ Ψ ∘ f) x = DP ∘ π_Q ∘ Df`, so it is onto whatever `DP ∘ π_Q ∘ Df` is onto (the submersion clause).
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

/-- FC32: postcomposition keeps equal values. -/
theorem comp_eq_comp_of_eq {M X Z : Type*} (Ψ : X → Z) {f : M → X} {p q : M} (h : f p = f q) :
    (Ψ ∘ f) p = (Ψ ∘ f) q := by
  simp only [Function.comp_apply, h]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The adjustment map along `Q` with smoothing map `P` and cutoff `ψ`. -/
noncomputable def adjustmentMap (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    (P : H → H) (ψ : H → ℝ) : H → H :=
  fun x => x + ψ x • (P (Q.starProjection x) - Q.starProjection x)

theorem adjustmentMap_apply (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    (P : H → H) (ψ : H → ℝ) (x : H) :
    adjustmentMap Q P ψ x = x + ψ x • (P (Q.starProjection x) - Q.starProjection x) := rfl

/-- FC32: the kernel of `Df` lies in the kernel of `D(Ψ ∘ f)` (inclusion only). -/
theorem ker_le_ker_of_hasFDerivAt_comp {E H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H'] [NormedSpace ℝ H'] {f : E → H} {Ψ : H → H'} {x : E}
    {Df : E →L[ℝ] H} {DΨ : H →L[ℝ] H'} (hf : HasFDerivAt f Df x) (hΨ : HasFDerivAt Ψ DΨ (f x)) :
    LinearMap.ker (Df : E →ₗ[ℝ] H) ≤ LinearMap.ker (fderiv ℝ (Ψ ∘ f) x : E →ₗ[ℝ] H') := by
  intro v hv
  have hv' : Df v = 0 := hv
  change fderiv ℝ (Ψ ∘ f) x v = 0
  rw [(hΨ.comp x hf).fderiv]
  change DΨ (Df v) = 0
  rw [hv', map_zero]

variable (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] [Qᗮ.HasOrthogonalProjection]

/-- FC32: the adjustment does not move the `Q⊥` coordinates. -/
theorem starProjection_orthogonal_adjustmentMap {P : H → H} (hP : ∀ z, P z ∈ Q) (ψ : H → ℝ)
    (x : H) : Qᗮ.starProjection (adjustmentMap Q P ψ x) = Qᗮ.starProjection x := by
  have hmem : P (Q.starProjection x) - Q.starProjection x ∈ Q :=
    Q.sub_mem (hP _) (Q.starProjection_apply_mem x)
  rw [adjustmentMap_apply, map_add, map_smul, Submodule.starProjection_orthogonal_apply_eq_zero hmem,
    smul_zero, add_zero]

omit [Qᗮ.HasOrthogonalProjection] in
/-- FC31 plateau: where the cutoff equals one, the `Q`-coordinates of the adjustment are `P` of the old ones. -/
theorem starProjection_adjustmentMap_of_eq_one {P : H → H} (hP : ∀ z, P z ∈ Q) {ψ : H → ℝ}
    {y : H} (hψ : ψ y = 1) : Q.starProjection (adjustmentMap Q P ψ y) = P (Q.starProjection y) := by
  rw [adjustmentMap_apply, hψ, one_smul, map_add, map_sub,
    (Submodule.starProjection_eq_self_iff).mpr (hP _),
    (Submodule.starProjection_eq_self_iff).mpr (Q.starProjection_apply_mem y)]
  abel

omit [Qᗮ.HasOrthogonalProjection] in
/-- FC31 submersion clause: where `ψ ∘ f = 1` near `x`, the derivative of the new `Q`-coordinates is
`DP ∘ π_Q ∘ Df`. -/
theorem hasFDerivAt_starProjection_adjustmentMap_of_eventually_eq_one {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {P : H → H} (hP : ∀ z, P z ∈ Q) {ψ : H → ℝ}
    {f : E → H} {x : E} {Df : E →L[ℝ] H} {DP : H →L[ℝ] H} (hf : HasFDerivAt f Df x)
    (hPd : HasFDerivAt P DP (Q.starProjection (f x))) (hone : ∀ᶠ y in 𝓝 x, ψ (f y) = 1) :
    HasFDerivAt (fun y => Q.starProjection (adjustmentMap Q P ψ (f y)))
      (DP.comp (Q.starProjection.comp Df)) x := by
  have hbase : HasFDerivAt (fun y => P (Q.starProjection (f y))) (DP.comp (Q.starProjection.comp Df)) x :=
    hPd.comp x (Q.starProjection.hasFDerivAt.comp x hf)
  apply hbase.congr_of_eventuallyEq
  filter_upwards [hone] with y hy
  exact starProjection_adjustmentMap_of_eq_one Q hP hy

omit [Qᗮ.HasOrthogonalProjection] in
/-- FC32 factorization: for `Q₃ ≤ Q₂` and a cutoff depending only on the `Q₂`-coordinates, the stage-three
adjustment factors over `π₂`. -/
theorem starProjection_adjustmentMap_of_le {Q₂ : Submodule ℝ H} [Q₂.HasOrthogonalProjection]
    (h32 : Q ≤ Q₂) {P : H → H} (hP : ∀ z, P z ∈ Q) (ψ' : H → ℝ) (x : H) :
    Q₂.starProjection (adjustmentMap Q P (ψ' ∘ Q₂.starProjection) x) =
      adjustmentMap Q P ψ' (Q₂.starProjection x) := by
  have hproj : Q.starProjection (Q₂.starProjection x) = Q.starProjection x := by
    have := congrArg (fun L : H →L[ℝ] H => L x) (Submodule.starProjection_comp_starProjection_of_le h32)
    simpa using this
  have hmem : P (Q.starProjection x) - Q.starProjection x ∈ Q₂ :=
    h32 (Q.sub_mem (hP _) (Q.starProjection_apply_mem x))
  rw [adjustmentMap_apply, adjustmentMap_apply, map_add, map_smul,
    (Submodule.starProjection_eq_self_iff).mpr hmem, hproj]
  rfl

end DifferentialGeometry.Analysis
