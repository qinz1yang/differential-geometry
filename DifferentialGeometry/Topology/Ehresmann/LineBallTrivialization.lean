import DifferentialGeometry.Topology.Ehresmann.BallTrivialization

/-!
# Proper submersions onto an open interval are trivial over smaller intervals

The one-dimensional companion of `exists_trivialization_over_planeBall_of_proper` (LC83's
supplier), needed by LFR20 item 2 (the slim packet is a trivial bundle over an interval).

* `lineBallOpens r`: the interval `(-r, r) = B(0, r) ⊂ ℝ` as an open set; `lineBallInner r R`:
  the interval `(-R, R)` inside it.
* `exists_trivialization_over_lineBall_of_proper`: a proper smooth submersion
  `f : M → (-r, r)` is trivial over every `(-R, R)`, `0 < R < r`: the inverse image of `(-R, R)` is
  diffeomorphic to (fibre over `0`) × `(-R, R)`, over the identity of `(-R, R)`, restricting to the
  identity on the zero fibre. The base flow is the translation flow of a cut-off unit field.
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Analysis.ODE DifferentialGeometry.Topology.Manifold

/-- The open interval `B(0, r) = (-r, r)` of `ℝ` as an open set. -/
def lineBallOpens (r : ℝ) : TopologicalSpace.Opens ℝ := ⟨ball 0 r, isOpen_ball⟩

theorem mem_lineBallOpens_iff {r s : ℝ} : s ∈ lineBallOpens r ↔ |s| < r := by
  change s ∈ ball (0 : ℝ) r ↔ _
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs]

theorem zero_mem_lineBallOpens {r : ℝ} (hr : 0 < r) : (0 : ℝ) ∈ lineBallOpens r :=
  mem_lineBallOpens_iff.mpr (by simpa using hr)

/-- The interval `(-R, R)` inside the manifold `(-r, r)`. -/
def lineBallInner (r R : ℝ) : TopologicalSpace.Opens (lineBallOpens r) :=
  ⟨Subtype.val ⁻¹' ball 0 R, isOpen_ball.preimage continuous_subtype_val⟩

theorem mem_lineBallInner_iff {r R : ℝ} {z : lineBallOpens r} :
    z ∈ lineBallInner r R ↔ |(z : ℝ)| < R := by
  change (z : ℝ) ∈ ball (0 : ℝ) R ↔ _
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

/-- A proper smooth submersion onto the open interval `(-r, r)` is trivial over every smaller
interval `(-R, R)`: the inverse image of `(-R, R)` is diffeomorphic to (fibre over `0`) ×
`(-R, R)`, over the identity of `(-R, R)` and restricting to the identity on the zero fibre. -/
theorem exists_trivialization_over_lineBall_of_proper {r : ℝ}
    (f : M → lineBallOpens r) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hp : IsProperMap f)
    (hreg : ∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ) f x)) {R : ℝ} (hR : 0 < R) (hRr : R < r) :
    let y₀ : lineBallOpens r := ⟨0, zero_mem_lineBallOpens (hR.trans hRr)⟩
    let _ := regularFiberChartedSpace f y₀ hf (fun x _ ↦ hreg x)
    let U : TopologicalSpace.Opens M :=
      ⟨f ⁻¹' lineBallInner r R, (lineBallInner r R).isOpen.preimage hf.continuous⟩
    ∃ (hy : y₀ ∈ lineBallInner r R) (Θ : Diffeomorph
        (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ).prod 𝓘(ℝ, ℝ)) I
        ({x : M // f x = y₀} × lineBallInner r R) U ∞),
      (∀ p, f (Θ p).1 = p.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1) := by
  intro y₀
  dsimp only
  have hy : y₀ ∈ lineBallInner r R := mem_lineBallInner_iff.mpr (by simpa [y₀] using hR)
  let N := lineBallOpens r
  let Q := lineBallInner r R
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := (2 * R + r) / 3, rOut := (R + 2 * r) / 3,
      rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  let V : ℝ → ℝ := fun w => b w • (1 : ℝ)
  have hV : ContDiff ℝ ∞ V := b.contDiff.smul contDiff_const
  have hVc : HasCompactSupport V := b.hasCompactSupport.smul_right
  have hVS : ∀ w ∈ ball (0 : ℝ) ((2 * R + r) / 3), V w = 1 := by
    intro w hw
    simp only [V, b.one_of_mem_closedBall (ball_subset_closedBall hw), one_smul]
  let Z : (z : N) → TangentSpace 𝓘(ℝ, ℝ) z := fun z => V z.1
  have hZ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun z : N => (⟨z, Z z⟩ : TangentBundle 𝓘(ℝ, ℝ) N)) :=
    DifferentialGeometry.VectorField.contMDiff_tangentSection_restrict_opens N
      (contMDiff_modelTangentSection_of_contDiff hV).contMDiffOn
  have hZc : IsCompact (tsupport Z) := by
    have hsub : tsupport V ⊆ (N : Set ℝ) := by
      intro w hw
      have hw' : w ∈ tsupport b := tsupport_smul_subset_left _ _ hw
      rw [b.tsupport_eq, mem_closedBall, dist_zero_right] at hw'
      change ‖w‖ ≤ (R + 2 * r) / 3 at hw'
      exact mem_lineBallOpens_iff.mpr (by rw [← Real.norm_eq_abs]; linarith)
    have hK : IsCompact (Subtype.val ⁻¹' tsupport V : Set N) := by
      rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
      have heq : tsupport V ∩ {x | x ∈ N} = tsupport V :=
        inter_eq_left.mpr (fun w hw => hsub hw)
      rw [heq]
      exact hVc
    exact hK.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset_preimage V continuous_subtype_val)
  obtain ⟨X, hXc, -, -, hflow⟩ := exists_compactlySupported_relatedFlow_of_surjective f hp hf hreg
    Z hZ hZc
  let d : ℝ → N ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ N := compactSupportFlowDiffeomorph Z hZ hZc
  let D : ℝ → M ≃ₘ⟮I, I⟯ M := compactSupportFlowDiffeomorph X X.contMDiff hXc
  have hbase : ∀ t (z : N), (d t z : ℝ) =
      compactSupportFlowDiffeomorph (I := 𝓘(ℝ, ℝ)) V
        (contMDiff_modelTangentSection_of_contDiff hV) hVc t z.1 := by
    intro t z
    exact compactSupportFlowDiffeomorph_map_of_mfderiv_eq (Subtype.val : N → ℝ)
      contMDiff_subtype_val Z hZ hZc V
      (contMDiff_modelTangentSection_of_contDiff hV) hVc
      (fun z => DifferentialGeometry.mfderiv_subtype_val_apply (I := 𝓘(ℝ, ℝ)) N z (Z z)) t z
  have htrans : ∀ t (z : N), ‖(z : ℝ)‖ < (2 * R + r) / 3 →
      ‖(z : ℝ) + t • (1 : ℝ)‖ < (2 * R + r) / 3 → (d t z : ℝ) = z + t • (1 : ℝ) := by
    intro t z hz hzt
    rw [hbase]
    exact compactSupportFlowDiffeomorph_eq_add_smul hV hVc isOpen_ball (convex_ball _ _)
      hVS (by rwa [mem_ball, dist_zero_right]) (by rwa [mem_ball, dist_zero_right])
  have hDj : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ D p.1 p.2) :=
    contMDiff_globalFlow_joint_of_compactSupport X X.contMDiff hXc
  have hDji : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ (D p.1).symm p.2) :=
    hDj.comp (contMDiff_fst.neg.prodMk contMDiff_snd)
  have hrel : ∀ t x, f (D t x) = d t (f x) := fun t x => hflow t x
  let σ : Q → ℝ := fun z => ((z : N) : ℝ)
  have hσ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ σ := contMDiff_subtype_val.comp contMDiff_subtype_val
  have hσy : σ ⟨y₀, hy⟩ = 0 := rfl
  have hσright : ∀ z : Q, d (σ z) y₀ = z.1 := by
    intro z
    have hzR : |((z : N) : ℝ)| < R := mem_lineBallInner_iff.mp z.2
    have hR3 : R < (2 * R + r) / 3 := by linarith
    have hy0 : ((y₀ : N) : ℝ) = 0 := rfl
    have hA : ‖((y₀ : N) : ℝ)‖ < (2 * R + r) / 3 := by
      rw [hy0, norm_zero]
      linarith
    have hB : ‖((y₀ : N) : ℝ) + σ z • (1 : ℝ)‖ < (2 * R + r) / 3 := by
      rw [hy0, zero_add, smul_eq_mul, mul_one, Real.norm_eq_abs]
      exact hzR.trans hR3
    apply Subtype.ext
    rw [htrans _ y₀ hA hB, hy0, zero_add, smul_eq_mul, mul_one]
  have hD0 : D 0 = Diffeomorph.refl I M ∞ :=
    compactSupportFlowDiffeomorph_zero X X.contMDiff hXc
  exact ⟨hy, exists_trivialization_of_related_family_of_section f hf hreg y₀ D d hDj hDji hrel Q
    hy σ hσ hσy hσright hD0⟩

end DifferentialGeometry.Topology.Ehresmann
