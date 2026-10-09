import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceOrientationNoncompact
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceFactorNoncompact
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.ProductDistance

/-!
# The smooth carrier of the NONCOMPACT LFR16 surface factor (LFR28 blocker B2)

`surfaceFactor_smoothCarrier` / `surfaceFactor_smoothCarrier_oriented` (F7-LFR11b G5a/G5b) need a
compact residual factor `W`. Compactness entered their proofs only through the compactness of the
zero factor `Z = {(e x).fst = 0}` and through LFR17; the carrier itself (model change
`Fin 2 → ℝ ⇝ 𝓡 2`, the smooth atlas of `exists_smoothCarrier_metric_with_derivative_orders`, the
pulled-back metric and its curvature, the G5b orientation) never used it. Here the carrier is
built over the SUBTYPE distance of `Z` (the smooth atlas does not depend on a metric), so that:

* `surfaceFactor_smoothCarrier_noncompact`: `S` is a smooth surface (model `𝓡 2`), complete and
  connected, `φ : S ≃ₜ Z` is `C^{k+2}` both ways and an isometry, `S ≃ᵢ W` through
  `x ↦ (e (φ x)).snd` (`dist_S = dist_W` through `e`), the pulled-back `C^{k+1}` metric `κ` has
  `sec ≥ 0`, and `(S, ⟨κ⟩)` is a Riemannian manifold (`IsRiemannianManifold`) whose tangent norm is
  the `κ`-norm — exactly the input shape of LFR24 (`finiteSurface_edge_model_core`).
* `surfaceFactor_smoothCarrier_oriented_noncompact`: the same, oriented from an orientation of `N`
  (`nonempty_orientation_of_splittingFactor_homeomorph`: F7-LFR11c's `splittingCarrierOrientation`
  applied to THIS carrier; F7-LFR11c's `surfaceFactor_oriented_smoothCarrier` orients a different
  carrier, without the metric clauses).
* `isRiemannianManifold_of_enorm_mfderiv_eq_cross`: a `C¹` bijection with `C¹` inverse between
  Riemannian manifolds over different models, norm-preserving on tangent vectors and an
  isometry of the given distances, transports `IsRiemannianManifold` backwards.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.ExactSplitting DifferentialGeometry.Manifold
  DifferentialGeometry.Topology.Manifold

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "P" => Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - Module.finrank ℝ ℝ) → ℝ

local instance nezero_finrank_euclidean_three_carrier_LFR28B12 :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

section Transport

variable {V E H H' M N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ E H'}
  [MetricSpace M] [ChartedSpace H M] [MetricSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun y : N => TangentSpace J y)]

/-- The inverse of a norm-preserving differentiable bijection preserves norms. -/
theorem enorm_mfderiv_inverse_eq_cross (f : M → N) (g : N → M)
    (hf : ∀ x, MDifferentiableAt I J f x) (hg : ∀ y, MDifferentiableAt J I g y)
    (hfg : ∀ y, f (g y) = y)
    (hiso : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J f x v‖ₑ = ‖v‖ₑ)
    (y : N) (w : TangentSpace J y) : ‖mfderiv J I g y w‖ₑ = ‖w‖ₑ := by
  have hd := mfderiv_comp y (hf (g y)) (hg y)
  have hid : f ∘ g = id := funext hfg
  rw [hid, mfderiv_id] at hd
  have hw : mfderiv I J f (g y) (mfderiv J I g y w) = w :=
    (congrArg (fun T => T w) hd).symm
  calc ‖mfderiv J I g y w‖ₑ = ‖mfderiv I J f (g y) (mfderiv J I g y w)‖ₑ :=
        (hiso (g y) _).symm
    _ = ‖w‖ₑ := by rw [hw, hfg y]

/-- **Cross-model transport of `IsRiemannianManifold`.** If `f : M → N` and `g : N → M` are
mutually inverse `C¹` maps, `f` preserves tangent norms and the distances, and `N` is a Riemannian
manifold, then so is `M`. -/
theorem isRiemannianManifold_of_enorm_mfderiv_eq_cross [IsRiemannianManifold J N]
    (f : M → N) (g : N → M) (hf : ContMDiff I J 1 f) (hg : ContMDiff J I 1 g)
    (hfg : ∀ y, f (g y) = y) (hgf : ∀ x, g (f x) = x)
    (hiso : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J f x v‖ₑ = ‖v‖ₑ)
    (hdist : ∀ x y, dist (f x) (f y) = dist x y) : IsRiemannianManifold I M := by
  have hiso' := enorm_mfderiv_inverse_eq_cross f g
    (fun x => (hf x).mdifferentiableAt one_ne_zero)
    (fun y => (hg y).mdifferentiableAt one_ne_zero) hfg hiso
  refine ⟨fun x y => ?_⟩
  have h1 : riemannianEDist J (f x) (f y) ≤ riemannianEDist I x y :=
    riemannianEDist_comp_le_of_enorm_mfderiv_eq_cross f hf hiso x y
  have h2 : riemannianEDist I (g (f x)) (g (f y)) ≤ riemannianEDist J (f x) (f y) :=
    riemannianEDist_comp_le_of_enorm_mfderiv_eq_cross g hg hiso' (f x) (f y)
  rw [hgf, hgf] at h2
  have hN : edist (f x) (f y) = riemannianEDist J (f x) (f y) :=
    IsRiemannianManifold.out (f x) (f y)
  have hed : edist (f x) (f y) = edist x y := by
    rw [edist_dist, edist_dist, hdist]
  rw [← hed, hN]
  exact le_antisymm h1 h2

end Transport

universe u v

/-- **The LFR11 orientation of ANY smooth carrier of the factor (rank one, dimension 3).** If
`S` is a smooth surface (model `𝓡 2`) and `φ : S ≃ₜ Z` is `C^{k+2}` both ways onto the zero factor
of an exact line splitting of an ORIENTED 3-manifold `N`, then `S` is orientable: F7-LFR11c's
`splittingCarrierOrientation` (ordered factor `∂_t` first, `lineSurfaceIndex`) applied to `φ`. -/
theorem nonempty_orientation_of_splittingFactor_homeomorph {N W : Type u} [MetricSpace N]
    [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N]
    [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [CompleteSpace N] [MetricSpace W] {k : ℕ}
    {S : Type v} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S]
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hk : 2 ≤ (k : ℕ∞))
    (hnorm : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)))
    (oN : ManifoldOrientation (𝓡 3) N 3) (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    letI := splittingFactorChartedSpace G hk hnorm e
    letI := splittingFactor_isManifold_one G hk hnorm e
    ∀ φ : S ≃ₜ {x : N // (e x).fst = 0},
      ContMDiff (𝓡 2) 𝓘(ℝ, P) ((k + 2 : ℕ) : ℕ∞ω) φ →
      ContMDiff 𝓘(ℝ, P) (𝓡 2) ((k + 2 : ℕ) : ℕ∞ω) φ.symm →
      Nonempty (ManifoldOrientation (𝓡 2) S 2) := by
  let _ := splittingFactorChartedSpace G hk hnorm e
  let _ := splittingFactor_isManifold_one G hk hnorm e
  intro φ hφ hφs
  have hr0 : ((k + 2 : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
  have h1k : (1 : ℕ∞ω) ≤ ((k + 2 : ℕ) : ℕ∞ω) := by exact_mod_cast (show 1 ≤ k + 2 by omega)
  have hDφ : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, P) φ x) := by
    intro x
    have hd := mfderiv_comp x (hφs.mdifferentiableAt hr0 (x := φ x))
      (hφ.mdifferentiableAt hr0 (x := x))
    have hid : (φ.symm : {x : N // (e x).fst = 0} → S) ∘ φ = id :=
      funext fun y => φ.symm_apply_apply y
    rw [hid, mfderiv_id] at hd
    intro a b hab
    exact (congrArg (fun L => L a) hd).trans
      ((congrArg (fun y => mfderiv 𝓘(ℝ, P) (𝓡 2) φ.symm (φ x) y) hab).trans
        (congrArg (fun L => L b) hd).symm)
  let oS := splittingCarrierOrientation G hk hnorm e (Module.Basis.singleton (Fin 1) ℝ)
    lineSurfaceIndex φ (hφ.of_le h1k) hDφ
    (smoothOrientationOfManifoldOrientation (𝓡 3) (manifoldOrientationCast (by simp) oN))
  obtain ⟨O, -⟩ := exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 2) oS
  exact ⟨manifoldOrientationCast (by simp) O⟩

/-- **B2: the smooth carrier of the noncompact surface factor.** For an exact line splitting
`e : N ≃ᵢ ℓ²(ℝ × W)` of a complete connected nonnegatively curved 3-manifold (ANY residual factor
`W`), the zero factor `Z` has a smooth carrier `S` (model `𝓡 2`) with the subtype distance: `S` is
complete and connected, `φ : S ≃ₜ Z` is `C^{k+2}` both ways and an isometry, `S ≃ᵢ W` through
`x ↦ (e (φ x)).snd`, the pulled-back `C^{k+1}` metric `κ` has `sec ≥ 0`, and with the bundle
`⟨κ⟩` the carrier is a Riemannian manifold whose tangent norm is the `κ`-norm. -/
theorem surfaceFactor_smoothCarrier_noncompact {N W : Type u} [MetricSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ, E3) ∞ N] [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [CompleteSpace N] [ConnectedSpace N]
    [SecondCountableTopology N] [MetricSpace W] {k : ℕ}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hk : 2 ≤ (k : ℕ∞))
    (hnorm : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)))
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    letI := splittingFactorChartedSpace G hk hnorm e
    letI := splittingFactor_isManifold_one G hk hnorm e
    ∃ (S : Type u) (_ : MetricSpace S) (_ : ChartedSpace E2 S) (_ : IsManifold (𝓡 2) ∞ S),
      CompleteSpace S ∧ ConnectedSpace S ∧
      ∃ φ : S ≃ₜ {x : N // (e x).fst = 0},
        ContMDiff (𝓡 2) 𝓘(ℝ, P) ((k + 2 : ℕ) : ℕ∞ω) φ ∧
        ContMDiff 𝓘(ℝ, P) (𝓡 2) ((k + 2 : ℕ) : ℕ∞ω) φ.symm ∧
        (∀ x y : S, dist (φ x) (φ y) = dist x y) ∧
        (∃ ψ : S ≃ᵢ W, ∀ x, ψ x = (e (φ x : N)).snd) ∧
        ∃ κ : ContMDiffRiemannianMetric (𝓡 2) ((k + 1 : ℕ) : ℕ∞ω) E2
            (TangentSpace (𝓡 2) : S → Type _),
          (∀ (x : S) (v w : TangentSpace (𝓡 2) x),
            κ.inner x v w = (inducedMetric G hk hnorm e).inner (φ x)
              (mfderiv (𝓡 2) 𝓘(ℝ, P) φ x v) (mfderiv (𝓡 2) 𝓘(ℝ, P) φ x w)) ∧
          (∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w) ∧
          (letI : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x) := ⟨κ.toRiemannianMetric⟩
           IsRiemannianManifold (𝓡 2) S ∧
           ∀ (x : S) (w : TangentSpace (𝓡 2) x),
             ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κ.inner x w w))) := by
  let _ := splittingFactorChartedSpace G hk hnorm e
  let _ := splittingFactor_isManifold_one G hk hnorm e
  let Z := {x : N // (e x).fst = 0}
  let _ : IsManifold 𝓘(ℝ, P) ((k + 2 : ℕ) : ℕ∞ω) Z :=
    withTop_natCast_add_two k ▸ splittingFactor_isManifold G hk hnorm e
  let L := splittingSurfaceModelEquiv
  let ZE := LinearModelChange Z L
  let _ : IsManifold (𝓡 2) ((k + 2 : ℕ) : ℕ∞ω) ZE := LinearModelChange.isManifold L
  let φ₀ : Diffeomorph (𝓡 2) 𝓘(ℝ, P) ZE Z ((k + 2 : ℕ) : ℕ∞ω) :=
    LinearModelChange.diffeomorph L
  let h' := inducedMetricNat G hk hnorm e
  obtain ⟨hE, -⟩ := exists_finite_order_pullback_metric_of_diffeomorph (k + 1) (k + 2)
    (k + 1) le_rfl le_rfl h' φ₀
  have hk2 : 2 ≤ k := by exact_mod_cast hk
  -- the smooth atlas (independent of any metric on `ZE`)
  obtain ⟨s, A, hA⟩ : ∃ (s : Set ZE) (A : SmoothCompatibleAtlas E2 ZE s),
      A.IsCompatible (chartAt E2 : ZE → OpenPartialHomeomorph ZE E2) (k + 1 + 1) := by
    let _ : LocallyCompactSpace ZE := ChartedSpace.locallyCompactSpace E2 ZE
    let _ : TopologicalSpace.MetrizableSpace ZE :=
      TopologicalSpace.metrizableSpace_of_t3_secondCountable ZE
    let _ : MetricSpace ZE := TopologicalSpace.metrizableSpaceMetric ZE
    obtain ⟨s, A, -, hA, -⟩ :=
      exists_smoothCarrier_metric_with_derivative_orders (E := E2) (X := ZE) (K := k + 1)
        (by omega) hE
    exact ⟨s, A, hA⟩
  -- the carrier over the subtype distance of `Z`
  let _ : MetricSpace ZE := (inferInstance : MetricSpace Z)
  let S := SmoothCarrier A
  have hCs : ContMDiff (𝓡 2) (𝓡 2) ((k + 2 : ℕ) : ℕ∞ω) (SmoothCarrier.toBase A) :=
    SmoothCarrier.contMDiff_toBase_of_chartAt A (chartAt E2) (fun y => mem_range_self y) hA
  have hCs' : ContMDiff (𝓡 2) (𝓡 2) ((k + 2 : ℕ) : ℕ∞ω) (SmoothCarrier.ofBase A) :=
    SmoothCarrier.contMDiff_ofBase_of_chartAt A (chartAt E2) (fun y => mem_range_self y) hA
  let f : Diffeomorph (𝓡 2) (𝓡 2) S ZE ((k + 2 : ℕ) : ℕ∞ω) :=
    ⟨SmoothCarrier.equivBase A, hCs, hCs'⟩
  let Φ : Diffeomorph (𝓡 2) 𝓘(ℝ, P) S Z ((k + 2 : ℕ) : ℕ∞ω) := f.trans φ₀
  have hS : IsManifold (𝓡 2) ((k + 1 + 1 : ℕ) : ℕ∞ω) S :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  obtain ⟨κ, hκ⟩ := exists_finite_order_pullback_metric_of_diffeomorph (k + 1) (k + 2) (k + 1)
    le_rfl le_rfl h' Φ
  have h3Z : IsManifold 𝓘(ℝ, P) 3 Z := IsManifold.of_le (n := ((k + 2 : ℕ) : ℕ∞ω))
    (by exact_mod_cast (show 3 ≤ k + 2 by omega))
  have hn2 : (2 : ℕ∞ω) ≤ ((k + 1 : ℕ) : ℕ∞ω) := by exact_mod_cast (show 2 ≤ k + 1 by omega)
  have hsecS : ∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w := by
    intro x v w
    rw [sectionalCurvature_eq_of_partialDiffeomorph_pullback_cross κ h' hn2 hn2
      (DifferentialGeometry.PartialDiffeomorph.ofLE Φ.toPartialDiffeomorph
        (by exact_mod_cast (show 3 ≤ k + 2 by omega)))
      (fun q _ v' w' => hκ q v' w') (mem_univ x) v w]
    exact inducedMetric_sectionalCurvature_nonneg G hk hnorm e hsec _ _ _
  have hinner : ∀ (x : S) (v w : TangentSpace (𝓡 2) x),
      κ.inner x v w = (inducedMetric G hk hnorm e).inner (Φ.toHomeomorph x)
        (mfderiv (𝓡 2) 𝓘(ℝ, P) Φ.toHomeomorph x v)
        (mfderiv (𝓡 2) 𝓘(ℝ, P) Φ.toHomeomorph x w) := by
    intro x v w
    rw [hκ, inducedMetricNat_inner G hk hnorm e]
    rfl
  -- completeness, connectedness, distances
  have hcZ : CompleteSpace ZE := completeSpace_splittingFactor e
  have hconnZ : ConnectedSpace Z := connectedSpace_splittingFactor e
  have hconnS : ConnectedSpace S :=
    Φ.toHomeomorph.symm.surjective.connectedSpace Φ.toHomeomorph.symm.continuous
  have hdist : ∀ x y : S, dist (Φ.toHomeomorph x) (Φ.toHomeomorph y) = dist x y :=
    fun _ _ => rfl
  let Φi : S ≃ᵢ Z := ⟨Φ.toHomeomorph.toEquiv, Isometry.of_dist_eq hdist⟩
  let ψ : S ≃ᵢ W := Φi.trans (splittingFactorEquiv e).symm
  have hψ : ∀ x, ψ x = (e (Φ.toHomeomorph x : N)).snd := fun _ => rfl
  -- the Riemannian structures
  let bZ : RiemannianBundle (fun z : Z => TangentSpace 𝓘(ℝ, P) z) :=
    ⟨(inducedMetric G hk hnorm e).toRiemannianMetric⟩
  have hRZ : IsRiemannianManifold 𝓘(ℝ, P) Z :=
    (surfaceFactor_of_exactSplitting_noncompact G hk hnorm hsec e).2.2.2.2.1
  let bS : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x) := ⟨κ.toRiemannianMetric⟩
  have h1S : IsManifold (𝓡 2) 1 S := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have hnormS : ∀ (x : S) (w : TangentSpace (𝓡 2) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κ.inner x w w)) :=
    fun x w => enorm_tangent_eq_sqrt_inner κ x w
  have hiso : ∀ (x : S) (v : TangentSpace (𝓡 2) x),
      ‖mfderiv (𝓡 2) 𝓘(ℝ, P) Φ.toHomeomorph x v‖ₑ = ‖v‖ₑ := by
    intro x v
    rw [enorm_tangent_eq_sqrt_inner (inducedMetric G hk hnorm e), hnormS, hinner]
  have h1 : (1 : ℕ∞ω) ≤ ((k + 2 : ℕ) : ℕ∞ω) := by exact_mod_cast (show 1 ≤ k + 2 by omega)
  have hRS : IsRiemannianManifold (𝓡 2) S :=
    isRiemannianManifold_of_enorm_mfderiv_eq_cross Φ.toHomeomorph Φ.toHomeomorph.symm
      (Φ.contMDiff.of_le h1) (Φ.symm.contMDiff.of_le h1) Φ.toHomeomorph.apply_symm_apply
      Φ.toHomeomorph.symm_apply_apply hiso hdist
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, hconnS,
    Φ.toHomeomorph, Φ.contMDiff, Φ.symm.contMDiff, hdist, ⟨ψ, hψ⟩, κ, hinner, hsecS,
    hRS, hnormS⟩

/-- **B2, oriented.** The carrier of `surfaceFactor_smoothCarrier_noncompact`, oriented from an
orientation `oN` of `N` (LFR11 orientation clause on this carrier). -/
theorem surfaceFactor_smoothCarrier_oriented_noncompact {N W : Type u} [MetricSpace N]
    [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N]
    [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [CompleteSpace N] [ConnectedSpace N]
    [SecondCountableTopology N] [MetricSpace W] {k : ℕ}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hk : 2 ≤ (k : ℕ∞))
    (hnorm : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)))
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    (oN : ManifoldOrientation (𝓡 3) N 3) (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    letI := splittingFactorChartedSpace G hk hnorm e
    letI := splittingFactor_isManifold_one G hk hnorm e
    ∃ (S : Type u) (_ : MetricSpace S) (_ : ChartedSpace E2 S) (_ : IsManifold (𝓡 2) ∞ S),
      CompleteSpace S ∧ ConnectedSpace S ∧ Nonempty (ManifoldOrientation (𝓡 2) S 2) ∧
      ∃ φ : S ≃ₜ {x : N // (e x).fst = 0},
        ContMDiff (𝓡 2) 𝓘(ℝ, P) ((k + 2 : ℕ) : ℕ∞ω) φ ∧
        ContMDiff 𝓘(ℝ, P) (𝓡 2) ((k + 2 : ℕ) : ℕ∞ω) φ.symm ∧
        (∀ x y : S, dist (φ x) (φ y) = dist x y) ∧
        (∃ ψ : S ≃ᵢ W, ∀ x, ψ x = (e (φ x : N)).snd) ∧
        ∃ κ : ContMDiffRiemannianMetric (𝓡 2) ((k + 1 : ℕ) : ℕ∞ω) E2
            (TangentSpace (𝓡 2) : S → Type _),
          (∀ (x : S) (v w : TangentSpace (𝓡 2) x),
            κ.inner x v w = (inducedMetric G hk hnorm e).inner (φ x)
              (mfderiv (𝓡 2) 𝓘(ℝ, P) φ x v) (mfderiv (𝓡 2) 𝓘(ℝ, P) φ x w)) ∧
          (∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w) ∧
          (letI : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x) := ⟨κ.toRiemannianMetric⟩
           IsRiemannianManifold (𝓡 2) S ∧
           ∀ (x : S) (w : TangentSpace (𝓡 2) x),
             ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κ.inner x w w))) := by
  let _ := splittingFactorChartedSpace G hk hnorm e
  let _ := splittingFactor_isManifold_one G hk hnorm e
  obtain ⟨S, mS, cS, iS, hc, hconn, φ, hφ, hφs, hdist, hψ, κ, hκ, hsecS, hR⟩ :=
    surfaceFactor_smoothCarrier_noncompact G hk hnorm hsec e
  exact ⟨S, mS, cS, iS, hc, hconn,
    nonempty_orientation_of_splittingFactor_homeomorph G hk hnorm oN e φ hφ hφs,
    φ, hφ, hφs, hdist, hψ, κ, hκ, hsecS, hR⟩

end DifferentialGeometry.Geometry.Collapse
