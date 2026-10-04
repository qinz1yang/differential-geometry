import DifferentialGeometry.Geometry.Curvature.Surface.DevelopingMapFlat
import DifferentialGeometry.Geometry.Curvature.Surface.FlatTorusLattice
import DifferentialGeometry.Geometry.Curvature.Surface.PeriodicGaussBonnetBinding
import DifferentialGeometry.Geometry.Metric.Path.Composition
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Distance of a flat surface with a periodic cover, through its developing map

Let `k` be a flat `C^n` (`n ≥ 2`) metric on a surface `M` whose distance is the Riemannian
distance, and `cov : E → M` a smooth onto local diffeomorphism from the model plane whose fibres
are the orbits of `ℤ v₁ + ℤ v₂` (a basis). With the developing map `φ : E ≃ₜ ℂ` of the pulled
back field (FT1) put `Ψ = cov ∘ φ⁻¹ : ℂ → M` and `Λ = ℤ l₁ + ℤ l₂` (the developed periods). Then
`Ψ` is onto, its fibres are the `Λ`-orbits, it is `1`-Lipschitz, and it realises every distance:
`dist (Ψ w) (Ψ w') = min_{λ ∈ Λ} ‖w − w' − λ‖`. The lower bound lifts `C¹` paths through the
covering map `Ψ` (lattice quotient, uniformly discrete `Λ`) and compares lengths with the
Euclidean plane (`IsRiemannianManifold 𝓘(ℝ, ℂ) ℂ`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace Bundle.ContMDiffRiemannianMetric

section Paths

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- A `C¹` map from the Euclidean plane whose differential preserves the norm does not increase
the Riemannian distance. -/
theorem riemannianEDist_comp_le_of_complex (f : ℂ → M) (hf : ContMDiff 𝓘(ℝ, ℂ) I 1 f)
    (hiso : ∀ (w : ℂ) (h : TangentSpace 𝓘(ℝ, ℂ) w), ‖mfderiv 𝓘(ℝ, ℂ) I f w h‖ₑ = ‖h‖ₑ)
    (w w' : ℂ) : riemannianEDist I (f w) (f w') ≤ riemannianEDist 𝓘(ℝ, ℂ) w w' := by
  refine le_of_forall_gt fun c hc => ?_
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hc
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ t :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun t ht =>
      ((hγ t (Ioo_subset_Icc_self ht)).contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
        one_ne_zero
  have heq : pathELength I (f ∘ γ) 0 1 = pathELength 𝓘(ℝ, ℂ) γ 0 1 :=
    Manifold.pathELength_comp_eq_of_enorm_mfderiv_eq f hdiff
      (ae_of_all _ fun t => (hf (γ t)).mdifferentiableAt one_ne_zero)
      (ae_of_all _ fun t => hiso (γ t) _)
  have hle : riemannianEDist I (f w) (f w') ≤ pathELength I (f ∘ γ) 0 1 :=
    riemannianEDist_le_pathELength (hf.comp_contMDiffOn hγ) (congrArg f hγ0) (congrArg f hγ1)
      zero_le_one
  rw [heq] at hle
  exact hle.trans_lt hlen

/-- **Lifting short paths.** Through a covering map `Ψ : ℂ → M` which is a `C¹` local
diffeomorphism with norm-preserving differential, a point at Riemannian distance `< r` from
`Ψ w` has a preimage at Euclidean distance `< r` from `w`. -/
theorem exists_lift_edist_lt {Ψ : ℂ → M} (hcov : IsCoveringMap Ψ)
    (hloc : IsLocalDiffeomorph 𝓘(ℝ, ℂ) I 1 Ψ)
    (hiso : ∀ (w : ℂ) (h : TangentSpace 𝓘(ℝ, ℂ) w), ‖mfderiv 𝓘(ℝ, ℂ) I Ψ w h‖ₑ = ‖h‖ₑ)
    {w : ℂ} {x' : M} {r : ℝ≥0∞} (hr : riemannianEDist I (Ψ w) x' < r) :
    ∃ w', Ψ w' = x' ∧ edist w w' < r := by
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hr
  have hγc : ContinuousOn γ (Icc 0 1) := hγ.continuousOn
  let γI : C(unitInterval, M) :=
    ⟨fun t => γ t, hγc.comp_continuous continuous_subtype_val fun t => t.2⟩
  have hγI0 : γI 0 = Ψ w := hγ0
  let Γ := hcov.liftPath γI w hγI0
  have hΓlift : Ψ ∘ Γ = γI := hcov.liftPath_lifts γI w hγI0
  have hΓ0 : Γ 0 = w := hcov.liftPath_zero γI w hγI0
  let G : ℝ → ℂ := fun t => Γ (projIcc 0 1 zero_le_one t)
  have hGc : Continuous G := Γ.continuous.comp continuous_projIcc
  have hGlift : ∀ t ∈ Icc (0 : ℝ) 1, Ψ (G t) = γ t := fun t ht => by
    have := congrFun hΓlift (projIcc 0 1 zero_le_one t)
    simpa [G, γI, projIcc_of_mem _ ht] using this
  have hGsmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 G (Icc 0 1) := by
    refine contMDiffOn_of_locally_contMDiffOn fun t ht => ?_
    have hf := hloc (G t)
    have hmaps : ∀ z ∈ hf.localInverse.target, Ψ z ∈ hf.localInverse.source := by
      intro z hz
      have h1 : Ψ z = hf.choose z := hf.choose_spec.2 hz
      rw [h1]
      exact hf.choose.map_source hz
    refine ⟨G ⁻¹' hf.localInverse.target, hf.localInverse.open_target.preimage hGc,
      hf.localInverse_mem_target, ?_⟩
    have heq : EqOn G (hf.localInverse ∘ γ) (Icc 0 1 ∩ G ⁻¹' hf.localInverse.target) := by
      intro s hs
      simp only [Function.comp_apply]
      rw [← hGlift s hs.1, hf.localInverse_left_inv hs.2]
    refine ContMDiffOn.congr ?_ heq
    refine hf.contMDiffOn_localInverse.comp (hγ.mono inter_subset_left) ?_
    intro s hs
    change γ s ∈ hf.localInverse.source
    rw [← hGlift s hs.1]
    exact hmaps _ hs.2
  have hG0 : G 0 = w := by simp [G, hΓ0]
  have hle1 : edist (G 0) (G 1) ≤ pathELength 𝓘(ℝ, ℂ) G 0 1 := by
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ, ℂ)) (G 0) (G 1)]
    exact riemannianEDist_le_pathELength hGsmooth rfl rfl zero_le_one
  have hdiffG : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) G t :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun t ht =>
      ((hGsmooth t (Ioo_subset_Icc_self ht)).contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
        one_ne_zero
  have heqlen : pathELength I (Ψ ∘ G) 0 1 = pathELength 𝓘(ℝ, ℂ) G 0 1 :=
    Manifold.pathELength_comp_eq_of_enorm_mfderiv_eq Ψ hdiffG
      (ae_of_all _ fun t => (hloc.contMDiff (G t)).mdifferentiableAt one_ne_zero)
      (ae_of_all _ fun t => hiso (G t) _)
  have hcongr : pathELength I (Ψ ∘ G) 0 1 = pathELength I γ 0 1 :=
    pathELength_congr fun t ht => hGlift t ht
  refine ⟨G 1, by rw [hGlift 1 ⟨zero_le_one, le_rfl⟩, hγ1], ?_⟩
  rw [← hG0]
  calc edist (G 0) (G 1) ≤ pathELength 𝓘(ℝ, ℂ) G 0 1 := hle1
    _ = pathELength I γ 0 1 := heqlen.symm.trans hcongr
    _ < r := hlen

end Paths

section Cover

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ∞ω}

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

omit [FiniteDimensional ℝ E] in
private theorem mem_sup_zmultiples_iff {l₁ l₂ l : ℂ} :
    l ∈ AddSubgroup.zmultiples l₁ ⊔ AddSubgroup.zmultiples l₂ ↔
      ∃ n₁ n₂ : ℤ, l = n₁ • l₁ + n₂ • l₂ := by
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨a, ha, c, hc, rfl⟩
    obtain ⟨n₁, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
    obtain ⟨n₂, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hc
    exact ⟨n₁, n₂, rfl⟩
  · rintro ⟨n₁, n₂, rfl⟩
    exact ⟨_, AddSubgroup.mem_zmultiples_iff.mpr ⟨n₁, rfl⟩, _,
      AddSubgroup.mem_zmultiples_iff.mpr ⟨n₂, rfl⟩, rfl⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M] in
private theorem mfderiv_add_period' {f : E → M} (hf : ContMDiff 𝓘(ℝ, E) I 1 f) {w : E}
    (hper : ∀ y, f (y + w) = f y) (y : E) :
    mfderiv 𝓘(ℝ, E) I f (y + w) = mfderiv 𝓘(ℝ, E) I f y := by
  have htr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E => z + w) y = ContinuousLinearMap.id ℝ E := by
    rw [mfderiv_eq_fderiv]
    exact ((hasFDerivAt_id y).add_const w).fderiv
  have hcomp := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := I)
    (f := fun z : E => z + w) (g := f) y (hf.mdifferentiable (by norm_num) (y + w))
    ((contDiff_id.add contDiff_const : ContDiff ℝ 1 (fun z : E => z + w)).contMDiff.mdifferentiable
      (by norm_num) y)
  have hfun : (f ∘ fun z : E => z + w) = f := funext hper
  rw [hfun, htr] at hcomp
  exact hcomp.symm

/-- **Distance of a flat surface with a periodic cover.** With `Ψ = cov ∘ φ⁻¹` (`φ` the developing
map of the pulled-back field) and `Λ` the developed period lattice: `Ψ` is onto, its fibres are the
`Λ`-orbits, it is `1`-Lipschitz, and every distance `dist (Ψ w) (Ψ w')` is realised as
`dist w w''` by a lift `w''` of `Ψ w'`. -/
theorem exists_developing_cover_of_flat (hE : Module.finrank ℝ E = 2)
    (k : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hnorm : ∀ x (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (√(k.inner x w w)))
    {cov : E → M} (hcov : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ cov) (hsurj : Surjective cov)
    {v₁ v₂ : E} (hli : LinearIndependent ℝ ![v₁, v₂]) (hper₁ : ∀ y, cov (y + v₁) = cov y)
    (hper₂ : ∀ y, cov (y + v₂) = cov y)
    (hfib : ∀ y y', cov y = cov y' → ∃ n₁ n₂ : ℤ, y' = y + (n₁ • v₁ + n₂ • v₂))
    (hflat : ∀ x v w, k.sectionalCurvature x v w = 0) :
    ∃ (Ψ : ℂ → M) (Λ : AddSubgroup ℂ), Surjective Ψ ∧ (∀ w, ∀ l ∈ Λ, Ψ (w + l) = Ψ w) ∧
      (∀ w w', Ψ w = Ψ w' → w' - w ∈ Λ) ∧ (∀ w w', dist (Ψ w) (Ψ w') ≤ dist w w') ∧
      ∀ w w', ∃ w'', Ψ w'' = Ψ w' ∧ dist (Ψ w) (Ψ w') = dist w w'' := by
  have : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by decide)
  -- the pulled-back field
  let B : E → E →L[ℝ] E →L[ℝ] ℝ := fun z => (k.inner (cov z) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
    (E := E) (F := E) (E' := E) (F' := E)
    (mfderiv 𝓘(ℝ, E) I cov z : E →L[ℝ] E) (mfderiv 𝓘(ℝ, E) I cov z : E →L[ℝ] E)
  have hsmooth : ContMDiff 𝓘(ℝ, E) I ∞ cov := hcov.contMDiff
  have hB : ContDiff ℝ 2 B := contDiffOn_univ.mp
    (contDiffOn_pullback_inner k hn (by decide : (2 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω)) isOpen_univ
      hsmooth.contMDiffOn)
  have hinjd : ∀ y, Injective (mfderiv 𝓘(ℝ, E) I cov y) := fun y =>
    ((hcov y).mfderivToContinuousLinearEquiv (by decide)).injective
  have hsymm : ∀ y u v, B y u v = B y v u := fun y u v => k.symm (cov y) _ _
  have hpos : ∀ y v, v ≠ 0 → 0 < B y v v := fun y v hv =>
    k.pos (cov y) _ (fun h => hv (hinjd y (h.trans (map_zero _).symm)))
  let Gf : M → (E →L[ℝ] E) → (E →L[ℝ] E →L[ℝ] ℝ) := fun p D =>
    (k.inner p : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (E := E) (F := E) (E' := E) (F' := E) D D
  have hperB : ∀ {w : E}, (∀ y, cov (y + w) = cov y) → ∀ y, B (y + w) = B y := by
    intro w hw y
    have h2 : (mfderiv 𝓘(ℝ, E) I cov (y + w) : E →L[ℝ] E) =
        (mfderiv 𝓘(ℝ, E) I cov y : E →L[ℝ] E) :=
      mfderiv_add_period' (hsmooth.of_le (by decide)) hw y
    change Gf (cov (y + w)) (mfderiv 𝓘(ℝ, E) I cov (y + w)) =
      Gf (cov y) (mfderiv 𝓘(ℝ, E) I cov y)
    exact congrArg₂ Gf (hw y) h2
  have hflatB : ∀ y, DifferentialGeometry.Analysis.coefficientSectional B y v₁ v₂ = 0 := by
    intro y
    rw [← sectionalCurvature_comp_eq_coefficientSectional k hn (by decide) (hcov y) v₁ v₂]
    exact hflat _ _ _
  -- the developing map
  obtain ⟨φ, φ', l₁, l₂, K, hφ, hφc, hin, hK, h₁, h₂⟩ :=
    DifferentialGeometry.Analysis.exists_developing_of_periodic_flat' hE hB hsymm hpos hli
      (hperB hper₁) (hperB hper₂) hflatB
  have hφC1 : ContDiff ℝ 1 φ := by
    refine contDiff_one_iff_fderiv.mpr ⟨fun y => (hφ y).differentiableAt, ?_⟩
    have : fderiv ℝ φ = fun y => (φ' y : E →L[ℝ] ℂ) := funext fun y => (hφ y).fderiv
    rw [this]
    exact hφc
  have hsymmC1 : ContDiff ℝ 1 φ.symm := φ.contDiff_symm hφ hφC1
  have hdsymm : ∀ w, HasFDerivAt φ.symm ((φ' (φ.symm w)).symm : ℂ →L[ℝ] E) w := fun w =>
    HasFDerivAt.of_local_left_inverse φ.symm.continuous.continuousAt (hφ (φ.symm w))
      (Filter.Eventually.of_forall fun z => φ.apply_symm_apply z)
  let Ψ : ℂ → M := fun w => cov (φ.symm w)
  let Λ : AddSubgroup ℂ := AddSubgroup.zmultiples l₁ ⊔ AddSubgroup.zmultiples l₂
  have hlatv : ∀ n₁ n₂ : ℤ, ∀ y, cov (y + (n₁ • v₁ + n₂ • v₂)) = cov y := fun n₁ n₂ =>
    ((show Function.Periodic cov v₁ from hper₁).zsmul n₁).add_period
      ((show Function.Periodic cov v₂ from hper₂).zsmul n₂)
  have hsymmlat : ∀ (n₁ n₂ : ℤ) w,
      φ.symm (w + (n₁ • l₁ + n₂ • l₂)) = φ.symm w + (n₁ • v₁ + n₂ • v₂) := by
    intro n₁ n₂ w
    rw [φ.symm_apply_eq, DifferentialGeometry.Analysis.apply_add_lattice h₁ h₂,
      φ.apply_symm_apply]
  have hinv : ∀ w, ∀ l ∈ Λ, Ψ (w + l) = Ψ w := by
    intro w l hl
    obtain ⟨n₁, n₂, rfl⟩ := mem_sup_zmultiples_iff.mp hl
    simp only [Ψ, hsymmlat, hlatv]
  have hfibΨ : ∀ w w', Ψ w = Ψ w' → w' - w ∈ Λ := by
    intro w w' h
    obtain ⟨n₁, n₂, hn⟩ := hfib _ _ h
    refine mem_sup_zmultiples_iff.mpr ⟨n₁, n₂, ?_⟩
    have := congrArg φ hn
    rw [φ.apply_symm_apply, DifferentialGeometry.Analysis.apply_add_lattice h₁ h₂,
      φ.apply_symm_apply] at this
    rw [this]
    abel
  have hsurjΨ : Surjective Ψ := by
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    exact ⟨φ y, by simp [Ψ]⟩
  -- `Ψ` is a `C¹` local diffeomorphism with isometric differential
  let Dφ : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ℂ E 1 :=
    { toEquiv := φ.symm.toEquiv
      contMDiff_toFun := hsymmC1.contMDiff
      contMDiff_invFun := hφC1.contMDiff }
  have hcov1 : ∀ y, IsLocalDiffeomorphAt 𝓘(ℝ, E) I 1 cov y := by
    intro y
    obtain ⟨Φ, hx, heq⟩ := hcov y
    exact ⟨DifferentialGeometry.PartialDiffeomorph.ofLE Φ (by decide), hx, heq⟩
  have hloc : IsLocalDiffeomorph 𝓘(ℝ, ℂ) I 1 Ψ := fun w =>
    (Dφ.isLocalDiffeomorph w).comp (hg := hcov1 _)
  have hiso : ∀ (w : ℂ) (h : TangentSpace 𝓘(ℝ, ℂ) w),
      ‖mfderiv 𝓘(ℝ, ℂ) I Ψ w h‖ₑ = ‖h‖ₑ := by
    intro w h
    have hc : MDifferentiableAt 𝓘(ℝ, E) I cov (φ.symm w) :=
      (hsmooth (φ.symm w)).mdifferentiableAt (by decide)
    have hs : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) φ.symm w :=
      (hsymmC1.contMDiff w).mdifferentiableAt one_ne_zero
    have hcomp : mfderiv 𝓘(ℝ, ℂ) I Ψ w = (mfderiv 𝓘(ℝ, E) I cov (φ.symm w)).comp
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) φ.symm w) := mfderiv_comp w hc hs
    have hsd : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) φ.symm w = ((φ' (φ.symm w)).symm : ℂ →L[ℝ] E) := by
      rw [mfderiv_eq_fderiv]
      exact (hdsymm w).fderiv
    let h' : ℂ := h
    have key : mfderiv 𝓘(ℝ, ℂ) I Ψ w h =
        mfderiv 𝓘(ℝ, E) I cov (φ.symm w) ((φ' (φ.symm w)).symm h') := by
      rw [hcomp, ContinuousLinearMap.comp_apply, hsd]
      rfl
    have happ : φ' (φ.symm w) ((φ' (φ.symm w)).symm h') = h' :=
      ContinuousLinearEquiv.apply_symm_apply _ _
    have hB' : k.inner (cov (φ.symm w))
        (mfderiv 𝓘(ℝ, E) I cov (φ.symm w) ((φ' (φ.symm w)).symm h'))
        (mfderiv 𝓘(ℝ, E) I cov (φ.symm w) ((φ' (φ.symm w)).symm h')) = ‖h'‖ ^ 2 := by
      have := hin (φ.symm w) ((φ' (φ.symm w)).symm h') ((φ' (φ.symm w)).symm h')
      rw [happ, real_inner_self_eq_norm_sq] at this
      exact this.symm
    rw [key, hnorm, hB', Real.sqrt_sq (norm_nonneg _), ofReal_norm,
      enorm_tangentSpace_vectorSpace]
    rfl
  have hcont : Continuous Ψ := hloc.contMDiff.continuous
  have hopen : IsOpenMap Ψ := hloc.isLocalHomeomorph.isOpenMap
  obtain ⟨μ, hμ, hgap⟩ := DifferentialGeometry.Analysis.exists_lattice_gap hE hli hφ hK h₁ h₂
  have hgapΛ : ∀ l ∈ Λ, l ≠ 0 → μ ≤ ‖l‖ := by
    intro l hl hne
    obtain ⟨n₁, n₂, rfl⟩ := mem_sup_zmultiples_iff.mp hl
    exact hgap n₁ n₂ hne
  have hcovering : IsCoveringMap Ψ :=
    DifferentialGeometry.Analysis.isCoveringMap_of_lattice_quotient hcont hopen hsurjΨ hinv
      hfibΨ hμ hgapΛ
  have hleE : ∀ w w', edist (Ψ w) (Ψ w') ≤ edist w w' := fun w w' => by
    rw [IsRiemannianManifold.out (I := I) (Ψ w) (Ψ w'),
      IsRiemannianManifold.out (I := 𝓘(ℝ, ℂ)) w w']
    exact riemannianEDist_comp_le_of_complex Ψ hloc.contMDiff hiso w w'
  have hle : ∀ w w', dist (Ψ w) (Ψ w') ≤ dist w w' := fun w w' => by
    have := hleE w w'
    rwa [edist_dist, edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at this
  refine ⟨Ψ, Λ, hsurjΨ, hinv, hfibΨ, hle, fun w w' => ?_⟩
  obtain ⟨m, hm⟩ := DifferentialGeometry.Analysis.exists_lattice_min hE hli hφ hK h₁ h₂ (w - w')
  have hw''Λ : m.1 • l₁ + m.2 • l₂ ∈ Λ := mem_sup_zmultiples_iff.mpr ⟨m.1, m.2, rfl⟩
  refine ⟨w' + (m.1 • l₁ + m.2 • l₂), hinv w' _ hw''Λ, le_antisymm ?_ ?_⟩
  · rw [← hinv w' _ hw''Λ]
    exact hle _ _
  · rw [← ENNReal.ofReal_le_ofReal_iff dist_nonneg, ← edist_dist, ← edist_dist]
    refine le_of_forall_gt fun r hr => ?_
    rw [IsRiemannianManifold.out (I := I)] at hr
    obtain ⟨w₃, hw₃, hlt⟩ := exists_lift_edist_lt hcovering hloc hiso hr
    obtain ⟨n₁, n₂, hn⟩ := mem_sup_zmultiples_iff.mp (hfibΨ w' w₃ hw₃.symm)
    have hnorm' : ‖w - (w' + (m.1 • l₁ + m.2 • l₂))‖ ≤ ‖w - w₃‖ := by
      have h := hm (n₁, n₂)
      rw [show w - (w' + (m.1 • l₁ + m.2 • l₂)) = w - w' - (m.1 • l₁ + m.2 • l₂) by abel,
        show w - w₃ = w - w' - (w₃ - w') by abel, hn]
      exact h
    calc edist w (w' + (m.1 • l₁ + m.2 • l₂)) ≤ edist w w₃ := by
          rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
          exact ENNReal.ofReal_le_ofReal hnorm'
      _ < r := hlt

end Cover

end Bundle.ContMDiffRiemannianMetric
