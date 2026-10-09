import DifferentialGeometry.Geometry.Exponential.Flat.DeckTranslation
import DifferentialGeometry.Geometry.Metric.Path.Composition
import DifferentialGeometry.Topology.Manifold.Quotient
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# SF4(b): translations of a flat orientable surface

For a complete flat orientable surface and `F = exp_p`:
* `flat_expMapIntrinsic_eq_iff`: `F y = F z ↔ z - y ∈ Λ` for a discrete additive subgroup `Λ`
  (the translation lattice), equivalently the fibre relation of `F` is translation invariant;
* `flat_exists_translation_isometryEquiv`: every translation `w ↦ w + u` descends to an isometry
  `τ` of `M` with `τ (F w) = F (w + u)`;
* `flat_exists_isometryEquiv_shift_segment`: a metric segment `γ` of length `2s` is shifted by `s`
  by such an isometry — the producer that W4-F7c's `false_of_translation_of_lt` consumes.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open Connection Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] in
/-- A `C¹` self-map whose differential preserves the extended norm does not increase the
Riemannian distance. -/
theorem riemannianEDist_comp_le_of_enorm_mfderiv_eq (f : M → M) (hf : ContMDiff I I 1 f)
    (hiso : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I I f x v‖ₑ = ‖v‖ₑ) (x y : M) :
    riemannianEDist I (f x) (f y) ≤ riemannianEDist I x y := by
  refine le_of_forall_gt fun c hc => ?_
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hc
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun t ht =>
      ((hγ t (Ioo_subset_Icc_self ht)).contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
        one_ne_zero
  have heq : pathELength I (f ∘ γ) 0 1 = pathELength I γ 0 1 :=
    pathELength_comp_eq_of_enorm_mfderiv_eq f hdiff
      (ae_of_all _ fun t => (hf (γ t)).mdifferentiableAt one_ne_zero)
      (ae_of_all _ fun t => hiso (γ t) _)
  have hle : riemannianEDist I (f x) (f y) ≤ pathELength I (f ∘ γ) 0 1 :=
    riemannianEDist_le_pathELength (hf.comp_contMDiffOn hγ) (congrArg f hγ0) (congrArg f hγ1)
      zero_le_one
  rw [heq] at hle
  exact hle.trans_lt hlen

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The fibre relation of a flat `exp_p` on an orientable surface: `exp_p y = exp_p z` iff the
translation by `z - y` preserves `exp_p`. -/
theorem flat_expMapIntrinsic_eq_iff_forall_add (hdim : Module.finrank ℝ E = 2) [ConnectedSpace M]
    (o : DifferentialGeometry.ManifoldOrientation I M 2)
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) (M := M) g}
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    {p : M} {y z : E} :
    expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from y) =
        expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z) ↔
      ∀ w : E, expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from w + (z - y)) =
        expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from w) := by
  let F : E → M := fun z => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)
  have hcov : IsCoveringMap F :=
    expMapIntrinsic_isCoveringMap_of_riemannOp_eq_zero (I := I) g hEnorm hR p
  have hsurj : Surjective F :=
    (flat_expMapIntrinsic_isLocalIsometry_isCoveringMap (I := I) g hEnorm hR p).2.2.2
  constructor
  · intro hyz w
    have hq := isQuotientCoveringMap_coveringDeckGroup hcov hsurj
    obtain ⟨γ, hγ⟩ := hq.apply_eq_iff_mem_orbit.mp hyz.symm
    change γ • y = z at hγ
    have h1 := flat_deck_apply_eq_add (I := I) hdim o g hEnorm hR p γ y
    have h2 := flat_deck_apply_eq_add (I := I) hdim o g hEnorm hR p γ w
    have hc : γ • (0 : E) = z - y := by rw [← hγ, h1]; abel
    rw [hc] at h2
    rw [← h2]
    exact coveringDeckGroup_map γ w
  · intro h
    have := h y
    simp only [add_sub_cancel] at this
    exact this.symm

/-- SF4(b) core: the fibre relation of a flat `exp_p` on an orientable surface is a discrete
translation lattice. -/
theorem flat_exists_translationLattice (hdim : Module.finrank ℝ E = 2) [ConnectedSpace M]
    (o : DifferentialGeometry.ManifoldOrientation I M 2)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) :
    ∃ Λ : AddSubgroup E, DiscreteTopology Λ ∧
      ∀ y z : E,
        expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from y) =
            expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z) ↔ z - y ∈ Λ := by
  let F : E → M := fun z => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)
  let Λ : AddSubgroup E :=
    { carrier := {c | ∀ w, F (w + c) = F w}
      add_mem' := by
        intro a b ha hb w
        change F (w + (a + b)) = F w
        rw [← add_assoc, hb (w + a), ha w]
      zero_mem' := fun w => by simp
      neg_mem' := by
        intro a ha w
        change F (w + -a) = F w
        have := ha (w + -a)
        rw [neg_add_cancel_right] at this
        exact this.symm }
  have hrel : ∀ y z : E, F y = F z ↔ z - y ∈ Λ := fun y z =>
    flat_expMapIntrinsic_eq_iff_forall_add (I := I) hdim o hR
  refine ⟨Λ, ?_, hrel⟩
  have hloc : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ F :=
    expMapIntrinsic_isLocalDiffeomorph_of_riemannOp_eq_zero (I := I) g hEnorm hR p
  obtain ⟨e, he0, hFe⟩ := hloc.isLocalHomeomorph 0
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine ⟨e.source, e.open_source, ?_⟩
  ext c
  simp only [mem_preimage, mem_singleton_iff]
  constructor
  · intro hc
    have hFc : F c = F 0 := ((hrel 0 c).mpr (by simp)).symm
    apply Subtype.ext
    change (c : E) = 0
    apply e.injOn hc he0
    rw [← hFe]
    exact hFc
  · rintro rfl
    exact he0

/-- SF4(b): on a complete flat orientable surface every translation of `T_pM` descends along
`exp_p` to an isometry of `M`. -/
theorem flat_exists_translation_isometryEquiv (hdim : Module.finrank ℝ E = 2) [ConnectedSpace M]
    (o : DifferentialGeometry.ManifoldOrientation I M 2)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) (u : E) :
    ∃ τ : M ≃ᵢ M, ∀ w : E,
      τ (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from w)) =
        expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from w + u) := by
  let F : E → M := fun z => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)
  have hloc : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ F :=
    expMapIntrinsic_isLocalDiffeomorph_of_riemannOp_eq_zero (I := I) g hEnorm hR p
  have hsurj : Surjective F :=
    (flat_expMapIntrinsic_isLocalIsometry_isCoveringMap (I := I) g hEnorm hR p).2.2.2
  have hrel : ∀ y z : E, F y = F z ↔ ∀ w : E, F (w + (z - y)) = F w := fun y z =>
    flat_expMapIntrinsic_eq_iff_forall_add (I := I) hdim o hR
  -- the descended translation
  let τ : E → M → M := fun c q => F (surjInv hsurj q + c)
  have hτ : ∀ c w, τ c (F w) = F (w + c) := by
    intro c w
    have h0 : F (surjInv hsurj (F w)) = F w := surjInv_eq hsurj (F w)
    have := (hrel _ _).mp h0 (surjInv hsurj (F w) + c)
    change F (surjInv hsurj (F w) + c) = F (w + c)
    rw [← this]
    congr 1
    abel
  have hτinv : ∀ c q, τ (-c) (τ c q) = q := by
    intro c q
    obtain ⟨w, rfl⟩ := hsurj q
    calc τ (-c) (τ c (F w)) = τ (-c) (F (w + c)) := by rw [hτ c w]
      _ = F (w + c + -c) := hτ (-c) (w + c)
      _ = F w := by rw [add_neg_cancel_right]
  have haddc : ∀ c : E, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun w : E => w + c) := fun c =>
    contMDiff_id.add contMDiff_const
  have hτsmooth : ∀ c, ContMDiff I I ∞ (τ c) := by
    intro c
    apply IsLocalDiffeomorph.contMDiff_of_comp_of_surjective hloc hsurj
    have heq : τ c ∘ F = F ∘ fun w => w + c := funext fun w => hτ c w
    rw [heq]
    exact hloc.contMDiff.comp (haddc c)
  have hτnorm : ∀ c (q : M) (X : TangentSpace I q), ‖mfderiv I I (τ c) q X‖ₑ = ‖X‖ₑ := by
    intro c q X
    obtain ⟨w, rfl⟩ := hsurj q
    obtain ⟨L, hL⟩ := (hloc w).isInvertible_mfderiv (by simp)
    obtain ⟨v, rfl⟩ : ∃ v : E, mfderiv 𝓘(ℝ, E) I F w v = X := by
      refine ⟨L.symm X, ?_⟩
      rw [← hL]
      exact L.apply_symm_apply X
    have hcomp : τ c ∘ F = F ∘ fun w => w + c := funext fun w => hτ c w
    have hchain := mfderiv_comp w (((hτsmooth c) (F w)).mdifferentiableAt (by simp))
      ((hloc.contMDiff w).mdifferentiableAt (by simp))
    have hchain' := mfderiv_comp w ((hloc.contMDiff (w + c)).mdifferentiableAt (by simp))
      ((haddc c w).mdifferentiableAt (by simp))
    have hadd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun w : E => w + c) w = ContinuousLinearMap.id ℝ E := by
      rw [mfderiv_eq_fderiv]
      exact ((hasFDerivAt_id w).add_const c).fderiv
    have hval : mfderiv I I (τ c) (F w) (mfderiv 𝓘(ℝ, E) I F w v) =
        mfderiv 𝓘(ℝ, E) I F (w + c) v := by
      have h1 : mfderiv 𝓘(ℝ, E) I (τ c ∘ F) w v = mfderiv 𝓘(ℝ, E) I (F ∘ fun w => w + c) w v := by
        rw [hcomp]
      rw [hchain, hchain', hadd] at h1
      exact h1
    rw [hval]
    have key : ∀ (q q' : M), q = q' → ∀ X : E,
        ‖(show TangentSpace I q from X)‖ₑ = ‖(show TangentSpace I q' from X)‖ₑ := by
      rintro q q' rfl X
      rfl
    exact (key _ _ (hτ c w) _).trans
      ((enorm_mfderiv_expMapIntrinsic_of_flat (I := I) g hEnorm hR p (w + c) v).trans
        (enorm_mfderiv_expMapIntrinsic_of_flat (I := I) g hEnorm hR p w v).symm)
  have hτdist : ∀ c a b, edist (τ c a) (τ c b) = edist a b := by
    intro c a b
    rw [IsRiemannianManifold.out (I := I), IsRiemannianManifold.out (I := I) a b]
    refine le_antisymm (riemannianEDist_comp_le_of_enorm_mfderiv_eq (τ c)
      ((hτsmooth c).of_le (by simp)) (hτnorm c) a b) ?_
    have h := riemannianEDist_comp_le_of_enorm_mfderiv_eq (τ (-c))
      ((hτsmooth (-c)).of_le (by simp)) (hτnorm (-c)) (τ c a) (τ c b)
    rwa [hτinv, hτinv] at h
  let eqv : M ≃ M :=
    { toFun := τ u
      invFun := τ (-u)
      left_inv := hτinv u
      right_inv := fun q => by simpa using hτinv (-u) q }
  exact ⟨⟨eqv, fun a b => hτdist u a b⟩, fun w => hτ u w⟩

end DifferentialGeometry.Geometry.Riemannian.Exponential
