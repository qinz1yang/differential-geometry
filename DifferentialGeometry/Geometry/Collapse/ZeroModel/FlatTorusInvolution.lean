import DifferentialGeometry.Geometry.Exponential.Flat.FlatTorusSmooth
import DifferentialGeometry.Geometry.Exponential.Flat.DeckTranslation
import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import DifferentialGeometry.Geometry.Collapse.ZeroModel.FlatTorusInvolutionLattice
import DifferentialGeometry.Geometry.Collapse.ZeroModel.FlatTorusDescent

/-!
# Free orientation-reversing isometric involutions of a flat torus

Lane LFR54-Q0, group G3 (the torus case of Q0, route of external review 41, §5). Let `S` be a
compact connected oriented surface with a smooth flat metric `g` and `τ` a smooth free involution
of `S` which is an isometry of `g` and reverses the orientation. Then there is a diffeomorphism
`Φ : ℝ/ℤ × ℝ/ℤ → S` with `Φ (x + ½, -y) = τ (Φ (x, y))`
(`exists_klein_diffeomorph_of_flat_involution`).

* `exists_isometric_periodic_cover_of_flat` (§5.1): ONE map `c = exp_p ∘ e⁻¹ : ℝ² → S` (`e` a
  linear isometry from `(T_p S, g_p)` to the Euclidean plane) is an onto covering local
  diffeomorphism, a local isometry from the Euclidean inner product, with fibres the cosets of a
  discrete full-rank lattice `Λ`;
* `contMDiff_of_comp_isLocalDiffeomorph`: a continuous map whose composite with a local
  diffeomorphism is smooth is smooth;
* `det_fderiv_neg_of_comp_eq_of_reverses`: a self-map of the plane covering an
  orientation-reversing map has negative Jacobian;
* the lift `σ` of `τ` through `c` (`IsCoveringMap.existsUnique_continuousMap_lifts`) is an affine
  isometry `σ z = A z + b` (Mazur–Ulam, `exists_affineIsometryEquiv_of_fderiv_norm_le`) with
  `A Λ ⊆ Λ`, `A² = 1`, `det A < 0`, `A b + b ∈ Λ` (`σ²` is a LATTICE TRANSLATION) and
  `A z + b - z ∉ Λ` (no fixed point on the quotient); the glide–lattice normal form
  (`exists_glide_lattice_normal_form`) and the periodic descent with its formula
  (`exists_diffeomorph_addCircle_prod_apply_of_periodic_cover`) give `Φ ([s], [t]) =
  c (q + s u + t v)`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Module
open scoped Manifold ContDiff Topology InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

omit [FiniteDimensional ℝ E] in
/-- A continuous map whose composite with a local diffeomorphism is smooth is smooth. -/
theorem contMDiff_of_comp_isLocalDiffeomorph {EA : Type*} [NormedAddCommGroup EA]
    [NormedSpace ℝ EA] {HA : Type*} [TopologicalSpace HA] {IA : ModelWithCorners ℝ EA HA}
    {A : Type*} [TopologicalSpace A] [ChartedSpace HA A]
    {c : E → M} (hc : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ c) {σ : A → E} (hσ : Continuous σ)
    (hcσ : ContMDiff IA I ∞ (c ∘ σ)) : ContMDiff IA 𝓘(ℝ, E) ∞ σ := by
  intro y
  let hq := hc (σ y)
  have hloc : ContMDiffAt IA 𝓘(ℝ, E) ∞ (hq.localInverse ∘ (c ∘ σ)) y :=
    hq.contMDiffAt_localInverse.comp y (hcσ y)
  apply hloc.congr_of_eventuallyEq
  filter_upwards [hσ.continuousAt (hq.localInverse.open_target.mem_nhds hq.localInverse_mem_target)]
    with z hz
  exact (hq.localInverse_left_inv hz).symm

variable [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem tangentOrientationEquiv_apply_symm_LFR54Q0 (e : E ≃ₗ[ℝ] E)
    (o : Orientation ℝ E (Fin (finrank ℝ E))) :
    tangentOrientationEquiv e (tangentOrientationEquiv e.symm o) = o := by
  have h := tangentOrientationEquiv_symm e.symm o
  rwa [LinearEquiv.symm_symm] at h

/-- **Orientation reversal lifts to a negative Jacobian.** A self-map `γ` of the model space with
`F ∘ γ = τ ∘ F`, for `F` smooth with bijective differentials into an oriented manifold and `τ`
orientation reversing, has negative Jacobian determinant everywhere. -/
theorem det_fderiv_neg_of_comp_eq_of_reverses {F : E → M} (hF : ContMDiff 𝓘(ℝ, E) I ∞ F)
    (hbij : ∀ z, Bijective (mfderiv 𝓘(ℝ, E) I F z)) (oM : SmoothOrientation I M)
    {τ : M → M} (hτ : ContMDiff I I ∞ τ) (hτbij : ∀ x, Bijective (mfderiv I I τ x))
    (hτrev : ∀ x, (pullbackSmoothOrientation I I τ hτ hτbij oM).val x = -oM.val x)
    {γ : E → E} (hγ : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) γ) (hγF : ∀ z, F (γ z) = τ (F z))
    (z : E) : LinearMap.det ((fderiv ℝ γ z : E →L[ℝ] E) : E →ₗ[ℝ] E) < 0 := by
  classical
  set D : E →L[ℝ] E := fderiv ℝ γ z with hD
  have hcomp : F ∘ γ = τ ∘ F := funext hγF
  have hchain : ∀ v, mfderiv 𝓘(ℝ, E) I F (γ z) (D v) =
      mfderiv I I τ (F z) (mfderiv 𝓘(ℝ, E) I F z v) := by
    intro v
    have h1 := mfderiv_comp_apply (x := z) ((hF (γ z)).mdifferentiableAt (by simp)) (hγ z) v
    have h2 := mfderiv_comp_apply (x := z) ((hτ (F z)).mdifferentiableAt (by simp))
      ((hF z).mdifferentiableAt (by simp)) v
    rw [hcomp] at h1
    have h3 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) γ z = D := by rw [hD, mfderiv_eq_fderiv]; rfl
    rw [← h3]
    exact h1.symm.trans h2
  let dF := differentialEquivOfBijective 𝓘(ℝ, E) I F hbij
  let dT := differentialEquivOfBijective I I τ hτbij
  have hinj : Injective D := by
    intro a a' h
    apply (hbij z).1
    apply (hτbij (F z)).1
    rw [← hchain a, ← hchain a', h]
  have hsurj : Surjective (D : E →ₗ[ℝ] E) := LinearMap.injective_iff_surjective.mp hinj
  let G : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective (D : E →ₗ[ℝ] E) ⟨hinj, hsurj⟩
  let O := pullbackSmoothOrientation 𝓘(ℝ, E) I F hF hbij oM
  have hO : ∀ w, O.val w = tangentOrientationEquiv (dF w).toLinearEquiv.symm (oM.val (F w)) :=
    fun w => by
      rw [pullbackSmoothOrientation_apply, ContinuousLinearEquiv.toLinearEquiv_symm]
  have hOz : oM.val (F z) = tangentOrientationEquiv (dF z).toLinearEquiv (O.val z) := by
    rw [hO z, tangentOrientationEquiv_apply_symm_LFR54Q0]
  have hrev : ∀ x, oM.val (τ x) = tangentOrientationEquiv (dT x).toLinearEquiv (-oM.val x) := by
    intro x
    have h := hτrev x
    rw [pullbackSmoothOrientation_apply, ContinuousLinearEquiv.toLinearEquiv_symm] at h
    rw [← h, tangentOrientationEquiv_apply_symm_LFR54Q0]
  -- `(dF (γ z))⁻¹ ∘ dT (F z) ∘ dF z = G`
  have hdiff : ((dF z).toLinearEquiv.trans (dT (F z)).toLinearEquiv).trans
      (dF (γ z)).toLinearEquiv.symm = G := by
    apply LinearEquiv.ext
    intro v
    apply (dF (γ z)).injective
    change dF (γ z) ((dF (γ z)).symm (dT (F z) (dF z v))) = dF (γ z) (D v)
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact (hchain v).symm
  have hkey : O.val (γ z) = -tangentOrientationEquiv G (O.val z) := by
    calc O.val (γ z)
        = tangentOrientationEquiv (dF (γ z)).toLinearEquiv.symm (oM.val (τ (F z))) := by
          rw [hO (γ z), hγF]
      _ = tangentOrientationEquiv (dF (γ z)).toLinearEquiv.symm
            (tangentOrientationEquiv (dT (F z)).toLinearEquiv
              (-tangentOrientationEquiv (dF z).toLinearEquiv (O.val z))) := by
          rw [hrev, hOz]
      _ = -tangentOrientationEquiv G (O.val z) := by
          rw [← hdiff, tangentOrientationEquiv_trans, tangentOrientationEquiv_trans,
            tangentOrientationEquiv_neg, tangentOrientationEquiv_neg]
  have hconst : O.val (γ z) = O.val z := smoothOrientation_model_apply_eq O (γ z) z
  rw [hconst, tangentOrientationEquiv_self] at hkey
  have hneg : Orientation.map (Fin (finrank ℝ E)) G (O.val z) = -O.val z := by
    nth_rewrite 2 [hkey]
    exact (neg_neg (Orientation.map (Fin (finrank ℝ E)) G (O.val z))).symm
  exact (Orientation.map_eq_neg_iff_det_neg (O.val z) G (by simp)).mp hneg

end General

section Flat

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S]
  [T2Space S] [CompactSpace S] [ConnectedSpace S]

private instance finrankTwoNeZero_LFR54Q0 : NeZero (Module.finrank ℝ E2) := ⟨by simp⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **The isometric periodic cover of a closed oriented flat surface** (review 41, §5.1). ONE map
`c = exp_p ∘ e⁻¹ : ℝ² → S`, `e : (T_p S, g_p) ≃ₗᵢ ℝ²`, is an onto covering local diffeomorphism,
a local isometry from the Euclidean inner product, whose fibres are the cosets of a discrete
full-rank lattice `Λ`. -/
theorem exists_isometric_periodic_cover_of_flat (o : SmoothOrientation (𝓡 2) S)
    (g : SmoothRiemannianMetric (𝓡 2) S)
    (hflat : ∀ x (v w z u : TangentSpace (𝓡 2) x), metricRm04StandardAt g x v w z u = 0) :
    ∃ (c : E2 → S) (Λ : Submodule ℤ E2) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ c ∧ IsCoveringMap c ∧ Surjective c ∧
      (∀ y v w : E2, g.inner (c y) (mfderiv (𝓡 2) (𝓡 2) c y v) (mfderiv (𝓡 2) (𝓡 2) c y w) =
        ⟪v, w⟫_ℝ) ∧
      ∀ y z, c y = c z ↔ z - y ∈ Λ := by
  let _ : IsManifold (𝓡 2) 1 S :=
    IsManifold.of_le (I := 𝓡 2) (M := S) (n := (∞ : WithTop ℕ∞)) (by decide)
  let _ : TopologicalSpace.MetrizableSpace S := Manifold.metrizableSpace (𝓡 2) S
  let _ : T3Space S := inferInstance
  let _ : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E2 (fun x : S => TangentSpace (𝓡 2) x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace S := EMetricSpace.ofRiemannianMetric (𝓡 2) S
  let _ : CompleteSpace S := (RiemannianMetricComplete.of_compact g).complete
  have hEg : Riemannian.IsMetricNorm (I := 𝓡 2) (M := S) g := fun z v =>
    Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓡 2) g z v
  have hR := ClosedSurface.riemannOp_eq_zero_of_rm04_eq_zero g hflat
  obtain ⟨O, -⟩ := exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 2) o
  let O2 : ManifoldOrientation (𝓡 2) S 2 :=
    Eq.rec (motive := fun m _ => ManifoldOrientation (𝓡 2) S m) O finrank_euclideanSpace_fin
  obtain ⟨p⟩ : Nonempty S := inferInstance
  let F : E2 → S := fun z =>
    Riemannian.Exponential.expMapIntrinsic (I := 𝓡 2) g hEg p (show TangentSpace (𝓡 2) p from z)
  obtain ⟨hloc, hisoF, hcovF, hsurjF⟩ :=
    Riemannian.Exponential.flat_expMapIntrinsic_isLocalIsometry_isCoveringMap (I := 𝓡 2) g hEg hR p
  obtain ⟨ΛF, hdiscF, hfibF⟩ :=
    Riemannian.Exponential.flat_exists_translationLattice (I := 𝓡 2) (by simp) O2 g hEg hR p
  -- Euclidean coordinates for `g_p`
  have hfr : finrank ℝ (TangentSpace (𝓡 2) p) = 2 := finrank_euclideanSpace_fin
  let eI : TangentSpace (𝓡 2) p ≃ₗᵢ[ℝ] E2 :=
    ((stdOrthonormalBasis ℝ (TangentSpace (𝓡 2) p)).reindex (finCongr hfr)).repr
  let eL : E2 ≃ₗ[ℝ] E2 := eI.toLinearEquiv
  let eE : E2 ≃L[ℝ] E2 := eL.toContinuousLinearEquiv
  let c : E2 → S := fun y => F (eE.symm y)
  have hcloc : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ c := fun y =>
    IsLocalDiffeomorphAt.comp (P := S) (𝓡 2) (eE.symm.toDiffeomorph.isLocalDiffeomorph y)
      (hloc _)
  have hccov : IsCoveringMap c := hcovF.comp_homeomorph eE.symm.toHomeomorph
  have hcsurj : Surjective c := hsurjF.comp eE.symm.surjective
  -- the lattice
  let Λ : Submodule ℤ E2 :=
    (ΛF.comap (eE.symm : E2 →L[ℝ] E2).toLinearMap.toAddMonoidHom).toIntSubmodule
  have hmem : ∀ x, x ∈ Λ ↔ eE.symm x ∈ ΛF := fun x => Iff.rfl
  have hfib : ∀ y z, c y = c z ↔ z - y ∈ Λ := fun y z => by
    rw [hmem, map_sub]
    exact hfibF _ _
  let f : Λ → ΛF := fun x => ⟨eE.symm x, x.property⟩
  have hdisc : DiscreteTopology Λ := DiscreteTopology.of_continuous_injective (f := f)
    ((eE.symm.continuous.comp continuous_subtype_val).subtype_mk _)
    (fun x x' h => Subtype.ext (eE.symm.injective (congrArg Subtype.val h)))
  -- cocompactness
  have hopen : ∀ n : ℕ, IsOpen (c '' Metric.ball (0 : E2) n) := fun n =>
    hcloc.isLocalHomeomorph.isOpenMap _ Metric.isOpen_ball
  have hcover : (univ : Set S) ⊆ ⋃ n : ℕ, c '' Metric.ball (0 : E2) n := by
    intro q _
    obtain ⟨y, rfl⟩ := hcsurj q
    obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
    exact mem_iUnion.mpr ⟨n, y, mem_ball_zero_iff.mpr hn, rfl⟩
  have hmono : Monotone fun n : ℕ => c '' Metric.ball (0 : E2) n := fun a b hab =>
    image_mono (Metric.ball_subset_ball (by exact_mod_cast hab))
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover _ hopen hcover hmono.directed_le
  have hcocpt : ∀ y : E2, ∃ l ∈ Λ, ‖y - l‖ ≤ n := by
    intro y
    obtain ⟨z, hz, hcz⟩ := hn (mem_univ (c y))
    refine ⟨y - z, (hfib z y).mp hcz, ?_⟩
    rw [sub_sub_cancel]
    exact (mem_ball_zero_iff.mp hz).le
  have hZ : IsZLattice ℝ Λ := FlatSurface.isZLattice_of_cocompact Λ hcocpt
  refine ⟨c, Λ, hdisc, hZ, hcloc, hccov, hcsurj, fun y v w => ?_, hfib⟩
  -- the isometry certificate
  have hlin : ∀ u : E2, mfderiv (𝓡 2) (𝓡 2) (fun x : E2 => eE.symm x) y u = eE.symm u := by
    intro u
    rw [mfderiv_eq_fderiv, ContinuousLinearEquiv.fderiv]
    rfl
  have hd : ∀ u : E2, mfderiv (𝓡 2) (𝓡 2) c y u =
      mfderiv (𝓡 2) (𝓡 2) F (eE.symm y) (eE.symm u) := by
    intro u
    have h := mfderiv_comp_apply (x := y) (g := F) (f := fun x : E2 => eE.symm x)
      ((hloc.contMDiff (eE.symm y)).mdifferentiableAt (by simp))
      (eE.symm.toDiffeomorph.contMDiff.mdifferentiableAt (by simp)) u
    rw [hlin] at h
    exact h
  rw [hd, hd, hisoF]
  change inner ℝ (eI.symm v) (eI.symm w) = _
  rw [← eI.inner_map_map, eI.apply_symm_apply, eI.apply_symm_apply]

/-- **G3 (T6).** A free orientation-reversing isometric involution of a compact connected oriented
surface with a smooth flat metric is conjugate to the Klein deck map `(x, y) ↦ (x + ½, -y)` of
`ℝ²/ℤ²`. -/
theorem exists_klein_diffeomorph_of_flat_involution (o : SmoothOrientation (𝓡 2) S)
    (g : SmoothRiemannianMetric (𝓡 2) S)
    (hflat : ∀ x (v w z u : TangentSpace (𝓡 2) x), metricRm04StandardAt g x v w z u = 0)
    (τ : S → S) (hτ : ContMDiff (𝓡 2) (𝓡 2) ∞ τ) (hτinv : ∀ x, τ (τ x) = x)
    (hτfree : ∀ x, τ x ≠ x)
    (hτiso : ∀ x (v w : TangentSpace (𝓡 2) x),
      g.inner (τ x) (mfderiv (𝓡 2) (𝓡 2) τ x v) (mfderiv (𝓡 2) (𝓡 2) τ x w) = g.inner x v w)
    (hτbij : ∀ x, Function.Bijective (mfderiv (𝓡 2) (𝓡 2) τ x))
    (hτrev : ∀ x, (pullbackSmoothOrientation (𝓡 2) (𝓡 2) τ hτ hτbij o).val x = -o.val x) :
    ∃ Φ : (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ≃ₘ⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), 𝓡 2⟯ S,
      ∀ x y : AddCircle (1 : ℝ),
        Φ (x + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -y) = τ (Φ (x, y)) := by
  obtain ⟨c, Λ, hdisc, hZ, hcloc, hccov, hcsurj, hciso, hfib⟩ :=
    exists_isometric_periodic_cover_of_flat o g hflat
  -- the lift `σ` of `τ` through `c`
  obtain ⟨e₀, he₀⟩ := hcsurj (τ (c 0))
  obtain ⟨σc, ⟨-, hσc⟩, -⟩ := hccov.existsUnique_continuousMap_lifts
    ⟨τ ∘ c, hτ.continuous.comp hcloc.contMDiff.continuous⟩ 0 e₀ he₀
  let σ : E2 → E2 := σc
  have hσ : ∀ y, c (σ y) = τ (c y) := fun y => congrFun hσc y
  have hσs : ContMDiff (𝓡 2) 𝓘(ℝ, E2) ∞ σ := by
    apply contMDiff_of_comp_isLocalDiffeomorph hcloc σc.continuous
    have h : c ∘ σ = τ ∘ c := funext hσ
    rw [h]
    exact hτ.comp hcloc.contMDiff
  -- `σ²` is a lattice translation
  have hσσ : ∀ y, σ (σ y) - y ∈ Λ := fun y =>
    (hfib y (σ (σ y))).mp (by rw [hσ, hσ, hτinv])
  let kσ : E2 → Λ := fun y => ⟨σ (σ y) - y, hσσ y⟩
  have hkσ : Continuous kσ :=
    ((σc.continuous.comp σc.continuous).sub continuous_id).subtype_mk _
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : E2, l₀ = σ (σ 0) := ⟨_, rfl⟩
  have hσσ' : ∀ y, σ (σ y) = y + l₀ := fun y => by
    have h := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hkσ (x := y) (y := 0))
    change σ (σ y) - y = σ (σ 0) - 0 at h
    rw [sub_zero, ← hl₀] at h
    rw [← h]
    abel
  have hl₀Λ : l₀ ∈ Λ := by
    have h := hσσ 0
    rwa [sub_zero, ← hl₀] at h
  -- `σ` is an affine isometry
  have hσinj : Injective σ := fun a a' h => by
    have h' := congrArg σ h
    rw [hσσ', hσσ'] at h'
    exact add_right_cancel h'
  let ψ : E2 → E2 := fun y => σ (y - l₀)
  have hσψ : ∀ y, σ (ψ y) = y := fun y => by
    change σ (σ (y - l₀)) = y
    rw [hσσ', sub_add_cancel]
  have hψσ : ∀ y, ψ (σ y) = y := fun y => hσinj (hσψ (σ y))
  let σE : E2 ≃ E2 := ⟨σ, ψ, hψσ, hσψ⟩
  have hσd : Differentiable ℝ σ :=
    (contMDiff_iff_contDiff.mp hσs).differentiable (by simp)
  have hψd : Differentiable ℝ ψ := fun y =>
    (hσd (y - l₀)).comp y (differentiableAt_id.sub_const l₀)
  have hchain : ∀ y v, mfderiv (𝓡 2) (𝓡 2) c (σ y) (fderiv ℝ σ y v) =
      mfderiv (𝓡 2) (𝓡 2) τ (c y) (mfderiv (𝓡 2) (𝓡 2) c y v) := by
    intro y v
    have h1 := mfderiv_comp_apply (x := y) ((hcloc.contMDiff (σ y)).mdifferentiableAt (by simp))
      ((hσs y).mdifferentiableAt (by simp)) v
    have h2 := mfderiv_comp_apply (x := y) ((hτ (c y)).mdifferentiableAt (by simp))
      ((hcloc.contMDiff y).mdifferentiableAt (by simp)) v
    have hcomp : c ∘ σ = τ ∘ c := funext hσ
    rw [hcomp] at h1
    have h3 : mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) σ y = fderiv ℝ σ y := by rw [mfderiv_eq_fderiv]; rfl
    rw [← h3]
    exact h1.symm.trans h2
  have key : ∀ (q q' : S) (a b a' b' : E2), q = q' → a = a' → b = b' →
      g.inner q a b = g.inner q' a' b' := by
    rintro q q' a b a' b' rfl rfl rfl
    rfl
  have hσn : ∀ y v, ‖fderiv ℝ σ y v‖ = ‖v‖ := by
    intro y v
    have hin : ⟪fderiv ℝ σ y v, fderiv ℝ σ y v⟫_ℝ = ⟪v, v⟫_ℝ := by
      rw [← hciso (σ y) (fderiv ℝ σ y v) (fderiv ℝ σ y v), ← hciso y v v,
        ← hτiso (c y) (mfderiv (𝓡 2) (𝓡 2) c y v) (mfderiv (𝓡 2) (𝓡 2) c y v)]
      exact key _ _ _ _ _ _ (hσ y) (hchain y v) (hchain y v)
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hin
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hin
  have hψn : ∀ y v, ‖fderiv ℝ ψ y v‖ = ‖v‖ := by
    intro y v
    have h : fderiv ℝ ψ y = fderiv ℝ σ (y - l₀) := fderiv_comp_sub (f := σ) l₀
    rw [h, hσn]
  obtain ⟨Aff, hAff⟩ := FlatSurface.exists_affineIsometryEquiv_of_fderiv_norm_le σE hσd
    (fun y v => (hσn y v).le) hψd (fun y v => (hψn y v).le)
  let A := Aff.linearIsometryEquiv
  have hσaff : ∀ z, σ z = A z + σ 0 := by
    intro z
    have h1 : Aff z = A z + Aff 0 := by simpa using Aff.map_vadd (0 : E2) z
    have hz : Aff z = σ z := congrFun hAff z
    have h0 : Aff 0 = σ 0 := congrFun hAff 0
    rw [← hz, ← h0, h1]
  -- the glide data
  have hAΛ : ∀ l ∈ Λ, A l ∈ Λ := by
    intro l hl
    have hc0 : c 0 = c l := (hfib 0 l).mpr (by rwa [sub_zero])
    have h := (hfib (σ 0) (σ l)).mp (by rw [hσ, hσ, hc0])
    rwa [hσaff l, add_sub_cancel_right] at h
  have hb : A (σ 0) + σ 0 = l₀ := by
    have h := hσσ' 0
    rw [hσaff (σ 0), zero_add] at h
    exact h
  have hA2 : ∀ z, A (A z) = z := by
    intro z
    have h := hσσ' z
    rw [hσaff (σ z), hσaff z, map_add, add_assoc, hb] at h
    exact add_right_cancel h
  have hfree : ∀ z, A z + σ 0 - z ∉ Λ := by
    intro z hz
    rw [← hσaff z] at hz
    apply hτfree (c z)
    rw [← hσ]
    exact ((hfib z (σ z)).mpr hz).symm
  have hcbij : ∀ w, Bijective (mfderiv (𝓡 2) (𝓡 2) c w) := fun w => by
    obtain ⟨L, hL⟩ := (hcloc w).isInvertible_mfderiv (by simp)
    rw [← hL]
    exact L.bijective
  have hdetσ := det_fderiv_neg_of_comp_eq_of_reverses hcloc.contMDiff hcbij o hτ hτbij hτrev
    (hσs.mdifferentiable (by simp)) hσ 0
  have hfdA : fderiv ℝ σ 0 = (A : E2 →L[ℝ] E2) := by
    have hfun : σ = fun z => A z + σ 0 := funext hσaff
    rw [hfun]
    exact ((A : E2 →L[ℝ] E2).hasFDerivAt.add_const (σ 0)).fderiv
  have hdet : LinearMap.det (A.toLinearEquiv : E2 →ₗ[ℝ] E2) < 0 := by
    rw [hfdA] at hdetσ
    exact hdetσ
  -- the normal form and the descent
  obtain ⟨u, v, q, j, hli, -, hmem, hAu, hAv, hq⟩ :=
    exists_glide_lattice_normal_form finrank_euclideanSpace_fin Λ A (σ 0) hAΛ hA2 hdet
      (by rw [hb]; exact hl₀Λ) hfree
  have hfib' : ∀ y z, c y = c z ↔ ∃ m n : ℤ, z - y = m • u + n • v := fun y z => by
    rw [hfib, hmem]
  obtain ⟨Φ, hΦ⟩ := exists_diffeomorph_addCircle_prod_apply_of_periodic_cover
    finrank_euclideanSpace_fin hcloc hcsurj hli hfib' q
  refine ⟨Φ, fun x y => ?_⟩
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
  change Φ (((s : ℝ) : AddCircle (1 : ℝ)) + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)),
    -((t : ℝ) : AddCircle (1 : ℝ))) = τ (Φ (((s : ℝ) : AddCircle (1 : ℝ)),
      ((t : ℝ) : AddCircle (1 : ℝ))))
  rw [← AddCircle.coe_add, ← AddCircle.coe_neg, hΦ, hΦ, ← hσ, hσaff]
  apply (hfib' _ _).mpr
  refine ⟨j, 0, ?_⟩
  have hAq : A q = ((j : ℝ) + 1 / 2) • u + q - σ 0 := by rw [← hq]; abel
  rw [map_add, map_add, LinearIsometryEquiv.map_smul, LinearIsometryEquiv.map_smul, hAu, hAv, hAq,
    ← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ]
  push_cast
  module

end Flat

end DifferentialGeometry.Geometry.Collapse.ZeroModel
