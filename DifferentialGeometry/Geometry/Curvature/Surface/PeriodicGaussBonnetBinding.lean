import DifferentialGeometry.Geometry.Curvature.Surface.PeriodicGaussBonnet
import DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetric
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCoefficients
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic
import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

/-!
# Periodic Gauss–Bonnet, binding: a `C²` metric with `K ≥ 0` on a periodic surface is flat

SF5 binding (LFR17's torus clause). For a `C^n` (`n ≥ 2`) Riemannian metric `k` on a surface `M`
modelled on a two-dimensional space `E`, and a smooth local diffeomorphism `cov : E → M` which is
onto and periodic along a basis `(v₁, v₂)`, nonnegative sectional curvature forces `K ≡ 0`: the
pulled-back coefficient field is `C²`, positive, symmetric and doubly periodic, its chart curvature
is the sectional curvature of `k` (`sectionalCurvature_comp_eq_coefficientSectional`, valid for any
local diffeomorphism from the model space), and the kernel
`coefficientSectional_eq_zero_of_periodic_of_nonneg` applies.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

section Cover

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 3 M] {n : ℕ∞ω}

private theorem coefficientSectional_congr_of_eventuallyEq
    {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (h : b =ᶠ[𝓝 x] c) (v w : E) :
    DifferentialGeometry.Analysis.coefficientSectional b x v w =
      DifferentialGeometry.Analysis.coefficientSectional c x v w := by
  have hG : DifferentialGeometry.Analysis.coefficientGram b =ᶠ[𝓝 x]
      DifferentialGeometry.Analysis.coefficientGram c :=
    h.mono fun y hy => congrArg (DifferentialGeometry.Analysis.coefficientGramCLM E) hy
  unfold DifferentialGeometry.Analysis.coefficientSectional
    DifferentialGeometry.Analysis.coefficientRm04
  rw [DifferentialGeometry.Analysis.jet2_congr_of_eventuallyEq hG, h.eq_of_nhds]

/-- **Chart curvature along a local diffeomorphism.** For a local diffeomorphism `f` from the
model space into `M`, the sectional curvature of `k` at `f y` on the image of a pair under `df_y`
is the chart curvature of the pulled-back coefficient field at `y`. -/
theorem sectionalCurvature_comp_eq_coefficientSectional
    (k : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    {m : ℕ∞ω} (hm : (3 : ℕ∞ω) ≤ m) {f : E → M} {y : E}
    (hf : IsLocalDiffeomorphAt 𝓘(ℝ, E) I m f y) (v w : E) :
    k.sectionalCurvature (f y) (mfderiv 𝓘(ℝ, E) I f y v) (mfderiv 𝓘(ℝ, E) I f y w) =
      DifferentialGeometry.Analysis.coefficientSectional
        (fun z => (k.inner (f z) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
          (E := E) (F := E) (E' := E) (F' := E)
          (mfderiv 𝓘(ℝ, E) I f z : E →L[ℝ] E) (mfderiv 𝓘(ℝ, E) I f z : E →L[ℝ] E)) y v w := by
  have hm0 : m ≠ 0 := fun h => by
    rw [h] at hm
    exact absurd hm (by decide)
  let Ψ := hf.localInverse
  let e : PartialDiffeomorph I 𝓘(ℝ, E) M E 3 := DifferentialGeometry.PartialDiffeomorph.ofLE Ψ hm
  have hes : ∀ z, e.symm z = Ψ.symm z := fun _ => rfl
  have hp : f y ∈ e.source := hf.localInverse_mem_source
  have hey : e (f y) = y := hf.localInverse_left_inv hf.localInverse_mem_target
  -- `e.symm` agrees with `f` on the open set `Ψ.target ∋ y`
  have hsymm_eq : ∀ z ∈ Ψ.target, e.symm z = f z := by
    intro z hz
    have hz' : Ψ.symm z ∈ Ψ.source := Ψ.map_target hz
    have h1 : Ψ (Ψ.symm z) = z := Ψ.right_inv hz
    have h2 := hf.localInverse_right_inv hz'
    rw [h1] at h2
    rw [hes]
    exact h2.symm
  have hnhds : Ψ.target ∈ 𝓝 y := Ψ.open_target.mem_nhds hf.localInverse_mem_target
  have hcoef : (fun z => (k.inner (e.symm z) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
        (mfderiv 𝓘(ℝ, E) I e.symm z : E →L[ℝ] E) (mfderiv 𝓘(ℝ, E) I e.symm z : E →L[ℝ] E)) =ᶠ[𝓝 y]
      (fun z => (k.inner (f z) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
        (E := E) (F := E) (E' := E) (F' := E)
        (mfderiv 𝓘(ℝ, E) I f z : E →L[ℝ] E) (mfderiv 𝓘(ℝ, E) I f z : E →L[ℝ] E)) := by
    filter_upwards [hnhds] with z hz
    have hev : (fun z => e.symm z) =ᶠ[𝓝 z] f :=
      Filter.eventuallyEq_of_mem (Ψ.open_target.mem_nhds hz) fun z' hz' => hsymm_eq z' hz'
    have hd : mfderiv 𝓘(ℝ, E) I e.symm z = mfderiv 𝓘(ℝ, E) I f z := hev.mfderiv_eq
    rw [hd, hsymm_eq z hz]
    rfl
  have hinv : ∀ u : E, mfderiv I 𝓘(ℝ, E) e (f y) (mfderiv 𝓘(ℝ, E) I f y u) = u := by
    intro u
    have hcomp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Ψ ∘ f) y =
        (mfderiv I 𝓘(ℝ, E) Ψ (f y)).comp (mfderiv 𝓘(ℝ, E) I f y) :=
      mfderiv_comp y (hf.mdifferentiableAt_localInverse hm0) (hf.mdifferentiableAt hm0)
    have hid : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Ψ ∘ f) y = ContinuousLinearMap.id ℝ E := by
      rw [hf.localInverse_eventuallyEq_left.mfderiv_eq]
      exact mfderiv_id
    have h := congrArg (fun L : E →L[ℝ] E => L u) (hcomp.symm.trans hid)
    exact h
  rw [sectionalCurvature_eq_coefficientSectional k hn e hp, hinv v, hinv w]
  rw [show e (f y) = y from hey]
  exact coefficientSectional_congr_of_eventuallyEq hcoef v w

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 3 M] in
private theorem mfderiv_add_period {f : E → M} (hf : ContMDiff 𝓘(ℝ, E) I 1 f) {w : E}
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

/-- **SF5 binding, periodic cover form.** A `C^n` (`n ≥ 2`) metric with nonnegative sectional
curvature on a surface admitting a smooth onto local diffeomorphism from its model plane, periodic
along a basis, is flat. -/
theorem sectionalCurvature_eq_zero_of_periodic_cover (hE : Module.finrank ℝ E = 2)
    (k : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    {cov : E → M} (hcov : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ cov) (hsurj : Surjective cov)
    {v₁ v₂ : E} (hli : LinearIndependent ℝ ![v₁, v₂]) (hper₁ : ∀ y, cov (y + v₁) = cov y)
    (hper₂ : ∀ y, cov (y + v₂) = cov y) (hK : ∀ x v w, 0 ≤ k.sectionalCurvature x v w) :
    ∀ x v w, k.sectionalCurvature x v w = 0 := by
  let B : E → E →L[ℝ] E →L[ℝ] ℝ := fun z => (k.inner (cov z) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
    (E := E) (F := E) (E' := E) (F' := E)
    (mfderiv 𝓘(ℝ, E) I cov z : E →L[ℝ] E) (mfderiv 𝓘(ℝ, E) I cov z : E →L[ℝ] E)
  have hF : ∀ y v w, k.sectionalCurvature (cov y) (mfderiv 𝓘(ℝ, E) I cov y v)
      (mfderiv 𝓘(ℝ, E) I cov y w) = DifferentialGeometry.Analysis.coefficientSectional B y v w :=
    fun y v w => sectionalCurvature_comp_eq_coefficientSectional k hn (by decide) (hcov y) v w
  have hsmooth : ContMDiff 𝓘(ℝ, E) I ∞ cov := hcov.contMDiff
  have hB : ContDiff ℝ 2 B := contDiffOn_univ.mp
    (contDiffOn_pullback_inner k hn (by decide : (2 : ℕ∞ω) + 1 ≤ ∞) isOpen_univ
      hsmooth.contMDiffOn)
  have hinj : ∀ y, Injective (mfderiv 𝓘(ℝ, E) I cov y) := fun y =>
    ((hcov y).mfderivToContinuousLinearEquiv (by decide)).injective
  have hsymm : ∀ y u v, B y u v = B y v u := fun y u v => k.symm (cov y) _ _
  have hpos : ∀ y v, v ≠ 0 → 0 < B y v v := fun y v hv =>
    k.pos (cov y) _ (fun h => hv (hinj y (h.trans (map_zero _).symm)))
  let G : M → (E →L[ℝ] E) → (E →L[ℝ] E →L[ℝ] ℝ) := fun p D =>
    (k.inner p : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (E := E) (F := E) (E' := E) (F' := E) D D
  have hper : ∀ {w : E}, (∀ y, cov (y + w) = cov y) → ∀ y, B (y + w) = B y := by
    intro w hw y
    have h2 : (mfderiv 𝓘(ℝ, E) I cov (y + w) : E →L[ℝ] E) =
        (mfderiv 𝓘(ℝ, E) I cov y : E →L[ℝ] E) :=
      mfderiv_add_period (hsmooth.of_le (by decide)) hw y
    change G (cov (y + w)) (mfderiv 𝓘(ℝ, E) I cov (y + w)) = G (cov y) (mfderiv 𝓘(ℝ, E) I cov y)
    exact congrArg₂ G (hw y) h2
  have hK' : ∀ y, 0 ≤ DifferentialGeometry.Analysis.coefficientSectional B y v₁ v₂ := fun y => by
    have h := hK (cov y) (mfderiv 𝓘(ℝ, E) I cov y v₁) (mfderiv 𝓘(ℝ, E) I cov y v₂)
    exact le_of_le_of_eq h (hF y v₁ v₂)
  have h0 := DifferentialGeometry.Analysis.coefficientSectional_eq_zero_of_periodic_of_nonneg hE hB
    hsymm hpos hli (hper hper₁) (hper hper₂) hK'
  intro x v w
  obtain ⟨y, rfl⟩ := hsurj x
  let L := (hcov y).mfderivToContinuousLinearEquiv (by decide)
  have hv : mfderiv 𝓘(ℝ, E) I cov y (L.symm v) = v := L.apply_symm_apply v
  have hw : mfderiv 𝓘(ℝ, E) I cov y (L.symm w) = w := L.apply_symm_apply w
  have h := hF y (L.symm v) (L.symm w)
  rw [hv, hw] at h
  rw [h]
  exact h0 y _ _

end Cover

section Torus

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem injective_mfderiv_coe_comp (L : E →L[ℝ] ℝ) (y : E) :
    ∀ u u', mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => (L z : AddCircle (1 : ℝ))) y u =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => (L z : AddCircle (1 : ℝ))) y u' → L u = L u' := by
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) (L y) :=
    AddCircle.contMDiff_coe.mdifferentiable (by simp) (L y)
  have hl : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => L z) y :=
    (L.contDiff (n := 1)).contMDiff.mdifferentiable (by simp) y
  have hcomp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => (L z : AddCircle (1 : ℝ))) y =
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) (L y)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => L z) y) :=
    mfderiv_comp (f := fun z => L z) (g := fun t : ℝ => (t : AddCircle (1 : ℝ))) y hc hl
  have hL : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => L z) y = L := by
    rw [mfderiv_eq_fderiv]
    exact L.fderiv
  intro u u' h
  rw [hcomp, hL] at h
  exact (AddCircle.bijective_mfderiv_coe (L y)).1 h

variable [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ∞ω}

/-- **SF5 binding, LFR17's torus clause.** A `C^n` (`n ≥ 2`) metric with nonnegative sectional
curvature on a surface diffeomorphic to `ℝ²/ℤ²` is flat. -/
theorem sectionalCurvature_eq_zero_of_diffeomorph_addCircle_prod (hE : Module.finrank ℝ E = 2)
    (k : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (Φ : (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ≃ₘ⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), I⟯ M)
    (hK : ∀ x v w, 0 ≤ k.sectionalCurvature x v w) :
    ∀ x v w, k.sectionalCurvature x v w = 0 := by
  have : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by decide)
  let T : E ≃L[ℝ] ℝ × ℝ := ContinuousLinearEquiv.ofFinrankEq (by simp [hE])
  let L₁ : E →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (T : E →L[ℝ] ℝ × ℝ)
  let L₂ : E →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (T : E →L[ℝ] ℝ × ℝ)
  let pair : E → AddCircle (1 : ℝ) × AddCircle (1 : ℝ) := fun z =>
    ((((T z).1 : ℝ) : AddCircle (1 : ℝ)), (((T z).2 : ℝ) : AddCircle (1 : ℝ)))
  have h₁ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun z => (((T z).1 : ℝ) : AddCircle (1 : ℝ))) :=
    AddCircle.contMDiff_coe.comp L₁.contDiff.contMDiff
  have h₂ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun z => (((T z).2 : ℝ) : AddCircle (1 : ℝ))) :=
    AddCircle.contMDiff_coe.comp L₂.contDiff.contMDiff
  have hpair : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ pair := h₁.prodMk h₂
  let cov : E → M := fun z => Φ (pair z)
  have hcovs : ContMDiff 𝓘(ℝ, E) I ∞ cov := Φ.contMDiff.comp hpair
  have hpair_inj : ∀ y, Injective (mfderiv 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) pair y) := by
    intro y u u' h
    rw [mfderiv_prodMk (h₁.mdifferentiableAt (by decide)) (h₂.mdifferentiableAt (by decide))]
      at h
    have e1 := injective_mfderiv_coe_comp L₁ y u u' (congrArg Prod.fst h)
    have e2 := injective_mfderiv_coe_comp L₂ y u u' (congrArg Prod.snd h)
    exact T.injective (Prod.ext e1 e2)
  have hcov_inj : ∀ y, Injective (mfderiv 𝓘(ℝ, E) I cov y) := by
    intro y
    have hcomp : mfderiv 𝓘(ℝ, E) I cov y =
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I Φ (pair y)).comp
          (mfderiv 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) pair y) :=
      mfderiv_comp (f := pair) (g := Φ) y (Φ.contMDiff.mdifferentiable (by decide) (pair y))
        (hpair.mdifferentiable (by decide) y)
    rw [hcomp, ContinuousLinearMap.coe_comp]
    exact ((Φ.mfderivToContinuousLinearEquiv (by decide) (pair y)).injective).comp
      (hpair_inj y)
  have hcov : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ cov :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv cov hcovs
      hcov_inj rfl
  have hsurj : Surjective cov := by
    intro x
    obtain ⟨⟨a, b⟩, hab⟩ := Φ.toEquiv.surjective x
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective b
    refine ⟨T.symm (s, t), ?_⟩
    simp only [cov, pair, ContinuousLinearEquiv.apply_symm_apply]
    exact hab
  have hT₁ : T (T.symm (1, 0)) = (1, 0) := T.apply_symm_apply _
  have hT₂ : T (T.symm (0, 1)) = (0, 1) := T.apply_symm_apply _
  have hli : LinearIndependent ℝ ![T.symm (1, 0), T.symm (0, 1)] := by
    refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
    have h := congrArg T hst
    rw [map_add, map_smul, map_smul, hT₁, hT₂, map_zero] at h
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero,
      zero_add, Prod.mk_eq_zero] at h
    exact h
  have hper₁ : ∀ y, cov (y + T.symm (1, 0)) = cov y := by
    intro y
    simp only [cov, pair, map_add, hT₁, Prod.fst_add, Prod.snd_add, add_zero,
      AddCircle.coe_add_period]
  have hper₂ : ∀ y, cov (y + T.symm (0, 1)) = cov y := by
    intro y
    simp only [cov, pair, map_add, hT₂, Prod.fst_add, Prod.snd_add, add_zero,
      AddCircle.coe_add_period]
  exact sectionalCurvature_eq_zero_of_periodic_cover hE k hn hcov hsurj hli hper₁ hper₂ hK

end Torus

end Bundle.ContMDiffRiemannianMetric
