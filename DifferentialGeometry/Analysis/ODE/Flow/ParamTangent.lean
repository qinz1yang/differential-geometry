import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.SpaceJets
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative
import DifferentialGeometry.Analysis.Calculus.TimeJet.Commutation
import DifferentialGeometry.Analysis.ODE.Flow.GlobalSliceSmoothness
import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.Variational.FiniteOrder

set_option autoImplicit false

noncomputable section

open Function Set
open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

def paramTangentVF
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : ℝ → X → X) :
    ℝ → (X × (P →L[ℝ] X)) → X × (P →L[ℝ] X) :=
  fun t z => (v t z.1, (fderiv ℝ (v t) z.1).comp z.2)

def paramTangentInitial
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a : P → X) (p : P) : X × (P →L[ℝ] X) :=
  (a p, fderiv ℝ a p)

def paramTangentCurve
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (γ : P → ℝ → X) (p : P) (t : ℝ) : X × (P →L[ℝ] X) :=
  (γ p t, fderiv ℝ (fun q => γ q t) p)

theorem paramTangentInitial_contDiffOn
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : Set P} (hA : IsOpen A) {a : P → X}
    (ha : ContDiffOn ℝ ∞ a A) :
    ContDiffOn ℝ ∞ (paramTangentInitial a) A := by
  have hDa : ContDiffOn ℝ ∞ (fun p => fderiv ℝ a p) A :=
    ha.fderiv_of_isOpen hA (by exact_mod_cast le_top)
  exact ha.prodMk hDa

@[simp]
theorem paramTangentVF_apply
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : ℝ → X → X) (t : ℝ) (x : X) (Z : P →L[ℝ] X) :
    paramTangentVF P v t (x, Z) = (v t x, (fderiv ℝ (v t) x).comp Z) := rfl

theorem paramTangentVF_contDiffOn
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {J : Set ℝ} (hJ : IsOpen J) {V : Set X} (hV : IsOpen V)
    {v : ℝ → X → X}
    (hv : ContDiffOn ℝ ∞ (uncurry v) (J ×ˢ V)) :
    ContDiffOn ℝ ∞ (uncurry (paramTangentVF P v))
      (J ×ˢ (V ×ˢ (Set.univ : Set (P →L[ℝ] X)))) := by
  let D : Set (ℝ × (X × (P →L[ℝ] X))) :=
    J ×ˢ (V ×ˢ (Set.univ : Set (P →L[ℝ] X)))
  let proj : ℝ × (X × (P →L[ℝ] X)) → ℝ × X := fun q => (q.1, q.2.1)
  have hproj : ContDiffOn ℝ ∞ proj D :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd) |>.contDiffOn
  have hprojMap : MapsTo proj D (J ×ˢ V) := fun _ hq => ⟨hq.1, hq.2.1⟩
  have hfirst : ContDiffOn ℝ ∞ (fun q : ℝ × (X × (P →L[ℝ] X)) =>
      v q.1 q.2.1) D := by
    exact hv.comp hproj hprojMap
  have hpartial : ContDiffOn ℝ ∞
      (fun q : ℝ × X => fderiv ℝ (v q.1) q.2) (J ×ˢ V) := by
    apply contDiffOn_partial_fderiv_of_succ_local (hJ.prod hV)
    exact hv.of_le (by simp)
  have hA : ContDiffOn ℝ ∞
      (fun q : ℝ × (X × (P →L[ℝ] X)) => fderiv ℝ (v q.1) q.2.1) D :=
    hpartial.comp hproj hprojMap
  have hZ : ContDiffOn ℝ ∞
      (fun q : ℝ × (X × (P →L[ℝ] X)) => q.2.2) D :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  have hpair : ContDiffOn ℝ ∞
      (fun q : ℝ × (X × (P →L[ℝ] X)) =>
        (fderiv ℝ (v q.1) q.2.1, q.2.2)) D :=
    hA.prodMk hZ
  have hcomp : ContDiff ℝ ∞
      (fun q : (X →L[ℝ] X) × (P →L[ℝ] X) => q.1.comp q.2) :=
    (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := P) (F := X) (G := X)).contDiff
  have hsecond : ContDiffOn ℝ ∞
      (fun q : ℝ × (X × (P →L[ℝ] X)) =>
        (fderiv ℝ (v q.1) q.2.1).comp q.2.2) D := by
    exact hcomp.contDiffOn.comp hpair (fun _ _ => mem_univ _)
  exact hfirst.prodMk hsecond

theorem paramTangentCurve_initial
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : Set P} (hA : IsOpen A) {t₀ : ℝ}
    {a : P → X} {γ : P → ℝ → X}
    (hγ : ∀ p ∈ A, γ p t₀ = a p) {p : P} (hp : p ∈ A) :
    paramTangentCurve γ p t₀ = paramTangentInitial a p := by
  have heq : (fun q => γ q t₀) =ᶠ[nhds p] a :=
    Filter.eventuallyEq_of_mem (hA.mem_nhds hp) hγ
  simp only [paramTangentCurve, paramTangentInitial, hγ p hp, heq.fderiv_eq]

theorem paramTangentCurve_initial_isIntegralCurveOn_of_contDiffOn
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : Set P} (hA : IsOpen A)
    {V : Set X} (hV : IsOpen V)
    {t₀ t₁ : ℝ} (ht₀₁ : t₀ ≤ t₁)
    {v : ℝ → X → X}
    (hv : ∀ t ∈ Icc t₀ t₁, DifferentiableOn ℝ (v t) V)
    {a : P → X} {γ : P → ℝ → X}
    (hγjoint : ContDiffOn ℝ ∞ (uncurry γ) (A ×ˢ Icc t₀ t₁))
    (hγ : ∀ p, p ∈ A →
      γ p t₀ = a p ∧ IsIntegralCurveOn (γ p) v (Icc t₀ t₁))
    (hstay : ∀ p ∈ A, ∀ t ∈ Icc t₀ t₁, γ p t ∈ V) :
    ∀ p ∈ A,
      paramTangentCurve γ p t₀ = paramTangentInitial a p ∧
      IsIntegralCurveOn (paramTangentCurve γ p) (paramTangentVF P v)
        (Icc t₀ t₁) := by
  intro p hp
  refine ⟨paramTangentCurve_initial hA (fun q hq => (hγ q hq).1) hp, ?_⟩
  rcases ht₀₁.eq_or_lt with rfl | ht₀₁
  · intro t ht
    have ht : t = t₀ := by simpa only [Icc_self, mem_singleton_iff] using ht
    subst t
    let h : HasDerivWithinAt (paramTangentCurve γ p)
        (paramTangentVF P v t₀ (paramTangentCurve γ p t₀)) {t₀} t₀ :=
      HasFDerivWithinAt.singleton
    simpa only [Icc_self] using h
  · let G : ℝ → P → X := fun t q => γ q t
    let swap : ℝ × P → P × ℝ := fun q => (q.2, q.1)
    have hswap_cd : ContDiffOn ℝ ∞ swap (Icc t₀ t₁ ×ˢ A) :=
      (contDiff_snd.prodMk contDiff_fst).contDiffOn
    have hswap_maps : MapsTo swap (Icc t₀ t₁ ×ˢ A)
        (A ×ˢ Icc t₀ t₁) := fun _ hq => ⟨hq.2, hq.1⟩
    have hG : ContDiffOn ℝ ∞ (uncurry G) (Icc t₀ t₁ ×ˢ A) := by
      let h : ContDiffOn ℝ ∞ (uncurry G) (Icc t₀ t₁ ×ˢ A) :=
        hγjoint.comp hswap_cd hswap_maps
      exact h
    have hUD : UniqueDiffOn ℝ (Icc t₀ t₁) := uniqueDiffOn_Icc ht₀₁
    have hsacc : Icc t₀ t₁ ⊆ closure (interior (Icc t₀ t₁)) := by
      rw [closure_interior_Icc (ne_of_lt ht₀₁)]
    have hDG : ContDiffOn ℝ ∞
        (uncurry (fun t q => fderiv ℝ (G t) q)) (Icc t₀ t₁ ×ˢ A) :=
      DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn hUD hA hG
    intro t ht
    have hZslice : ContDiffOn ℝ ∞
        (fun s => fderiv ℝ (fun q => γ q s) p) (Icc t₀ t₁) := by
      let h : ContDiffOn ℝ ∞
          (fun s => fderiv ℝ (fun q => γ q s) p) (Icc t₀ t₁) :=
        hDG.comp (contDiff_id.prodMk contDiff_const).contDiffOn
          (fun s hs => ⟨hs, hp⟩)
      exact h
    have hZderiv : HasDerivWithinAt
        (fun s => fderiv ℝ (fun q => γ q s) p)
        (derivWithin (fun s => fderiv ℝ (fun q => γ q s) p)
          (Icc t₀ t₁) t)
        (Icc t₀ t₁) t :=
      (hZslice.differentiableOn (by simp) t ht).hasDerivWithinAt
    have hcomm := DifferentialGeometry.Analysis.fderiv_derivWithin_time_comm
      hUD hsacc hA ht hp hG
    have hevol : Set.EqOn
        (fun q => derivWithin (fun s => γ q s) (Icc t₀ t₁) t)
        (fun q => v t (γ q t)) A := by
      intro q hq
      exact ((hγ q hq).2 t ht).derivWithin (hUD t ht)
    have hevol_nhds :
        (fun q => derivWithin (fun s => γ q s) (Icc t₀ t₁) t)
          =ᶠ[nhds p] (fun q => v t (γ q t)) :=
      Filter.eventuallyEq_of_mem (hA.mem_nhds hp) hevol
    have hγslice : ContDiffOn ℝ ∞ (fun q => γ q t) A := by
      exact hγjoint.comp (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun q hq => ⟨hq, ht⟩)
    have hγdiff : DifferentiableAt ℝ (fun q => γ q t) p :=
      (hγslice.contDiffAt (hA.mem_nhds hp)).differentiableAt (by simp)
    have hvdiff : DifferentiableAt ℝ (v t) (γ p t) :=
      (hv t ht (γ p t) (hstay p hp t ht)).differentiableAt
        (hV.mem_nhds (hstay p hp t ht))
    have hchain : fderiv ℝ (fun q => v t (γ q t)) p =
        (fderiv ℝ (v t) (γ p t)).comp
          (fderiv ℝ (fun q => γ q t) p) := by
      let h : fderiv ℝ (fun q => v t (γ q t)) p =
          (fderiv ℝ (v t) (γ p t)).comp
            (fderiv ℝ (fun q => γ q t) p) :=
        fderiv_comp p hvdiff hγdiff
      exact h
    have hZeq :
        derivWithin (fun s => fderiv ℝ (fun q => γ q s) p)
            (Icc t₀ t₁) t =
          (fderiv ℝ (v t) (γ p t)).comp
            (fderiv ℝ (fun q => γ q t) p) := by
      rw [← hcomm, hevol_nhds.fderiv_eq, hchain]
    have hstate := (hγ p hp).2 t ht
    let h : HasDerivWithinAt (paramTangentCurve γ p)
        (paramTangentVF P v t (paramTangentCurve γ p t)) (Icc t₀ t₁) t :=
      hstate.prodMk (hZderiv.congr_deriv hZeq)
    exact h

theorem paramTangentCurve_initial_isIntegralCurveOn
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {A : Set P} (hA : IsOpen A)
    {J : Set ℝ} (hJ : IsOpen J)
    {V : Set X} (hV : IsOpen V)
    {t₀ t₁ : ℝ} (ht₀₁ : t₀ ≤ t₁) (hI : Icc t₀ t₁ ⊆ J)
    {v : ℝ → X → X}
    (hv : ContDiffOn ℝ ∞ (uncurry v) (J ×ˢ V))
    {a : P → X} (ha : ContDiffOn ℝ ∞ a A)
    {γ : P → ℝ → X}
    (hγ : ∀ p, p ∈ A →
      γ p t₀ = a p ∧ IsIntegralCurveOn (γ p) v (Icc t₀ t₁))
    (hstay : ∀ p ∈ A, ∀ t ∈ Icc t₀ t₁, γ p t ∈ V) :
    ∀ p ∈ A,
      paramTangentCurve γ p t₀ = paramTangentInitial a p ∧
      IsIntegralCurveOn (paramTangentCurve γ p) (paramTangentVF P v)
        (Icc t₀ t₁) := by
  have hγjoint : ContDiffOn ℝ ∞ (uncurry γ) (A ×ˢ Icc t₀ t₁) :=
    contDiffOn_solutionFamily_of_stays hJ hV hv hA hI ha hγ
      (fun p hp t ht => hstay p hp t ht)
  apply paramTangentCurve_initial_isIntegralCurveOn_of_contDiffOn hA hV ht₀₁
    (v := v) ?_ hγjoint hγ hstay
  intro t ht
  have hv_slice : ContDiffOn ℝ ∞ (v t) V :=
    hv.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x hx => ⟨hI ht, hx⟩)
  exact hv_slice.differentiableOn (by simp)


theorem fderiv_paramTangentVF_apply
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : ℝ → X → X) (t : ℝ) (x h : X) (Z H : P →L[ℝ] X)
    (hv : DifferentiableAt ℝ (v t) x)
    (hDv : DifferentiableAt ℝ (fderiv ℝ (v t)) x) :
    fderiv ℝ (paramTangentVF P v t) (x,Z) (h,H) =
      (fderiv ℝ (v t) x h,
        (fderiv ℝ (v t) x).comp H + (fderiv ℝ (fderiv ℝ (v t)) x h).comp Z) := by
  have hfirst := hv.hasFDerivAt.comp (x,Z)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (x,Z)))
  have hmatrix := hDv.hasFDerivAt.comp (x,Z)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (x,Z)))
  have hsecond := hmatrix.clm_comp (hasFDerivAt_snd (𝕜 := ℝ) (p := (x,Z)))
  have hboth := hfirst.prodMk hsecond
  change HasFDerivAt (paramTangentVF P v t) _ (x,Z) at hboth
  rw [hboth.fderiv]
  rfl


end Flow
end ODE
end Analysis

namespace CheegerGromovCompactness


theorem MapCInfConvergenceOnCompacts.paramTangentInitial
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : Set P} (hA : IsOpen A)
    {a : ℕ → P → X} {aInf : P → X}
    (ha_cd : ∀ n, ContDiffOn ℝ ∞ (a n) A)
    (haInf_cd : ContDiffOn ℝ ∞ aInf A)
    (ha_convergence : MapCInfConvergenceOnCompacts A a aInf) :
    MapCInfConvergenceOnCompacts A
      (fun n p => Analysis.ODE.Flow.paramTangentInitial (a n) p)
      (fun p => Analysis.ODE.Flow.paramTangentInitial aInf p) := by
  have hderiv_convergence : MapCInfConvergenceOnCompacts A
      (fun n p => fderiv ℝ (a n) p) (fun p => fderiv ℝ aInf p) :=
    MapCInfConvergenceOnCompacts.fderivOn hA ha_convergence ha_cd haInf_cd
  have hderiv_cd : ∀ n, ContDiffOn ℝ ∞ (fun p => fderiv ℝ (a n) p) A :=
    fun n => (ha_cd n).fderiv_of_isOpen hA (by exact_mod_cast le_top)
  have hderivInf_cd : ContDiffOn ℝ ∞ (fun p => fderiv ℝ aInf p) A :=
    haInf_cd.fderiv_of_isOpen hA (by exact_mod_cast le_top)
  simpa only [Analysis.ODE.Flow.paramTangentInitial] using
    mapCInfConvergence_prodMk hA ha_convergence hderiv_convergence ha_cd haInf_cd
      hderiv_cd hderivInf_cd

theorem MapCInfConvergenceOnCompacts.paramTangentVF
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {J : Set ℝ} (hJ : IsOpen J) {V : Set X} (hV : IsOpen V)
    {v : ℕ → ℝ → X → X} {vInf : ℝ → X → X}
    (hv_cd : ∀ n, ContDiffOn ℝ ∞ (uncurry (v n)) (J ×ˢ V))
    (hvInf_cd : ContDiffOn ℝ ∞ (uncurry vInf) (J ×ˢ V))
    (hv_convergence : MapCInfConvergenceOnCompacts (J ×ˢ V)
      (fun n q => v n q.1 q.2) (fun q => vInf q.1 q.2)) :
    MapCInfConvergenceOnCompacts
      (J ×ˢ (V ×ˢ (Set.univ : Set (P →L[ℝ] X))))
      (fun n q => Analysis.ODE.Flow.paramTangentVF P (v n) q.1 q.2)
      (fun q => Analysis.ODE.Flow.paramTangentVF P vInf q.1 q.2) := by
  let Ω : Set (ℝ × X) := J ×ˢ V
  let D : Set (ℝ × (X × (P →L[ℝ] X))) :=
    J ×ˢ (V ×ˢ (Set.univ : Set (P →L[ℝ] X)))
  let proj : ℝ × (X × (P →L[ℝ] X)) → ℝ × X := fun q => (q.1, q.2.1)
  have hΩ : IsOpen Ω := hJ.prod hV
  have hD : IsOpen D := hJ.prod (hV.prod isOpen_univ)
  have hproj_cd : ContDiffOn ℝ ∞ proj D :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd) |>.contDiffOn
  have hprojMap : MapsTo proj D Ω := fun _ hq => ⟨hq.1, hq.2.1⟩
  have hproj_convergence : MapCInfConvergenceOnCompacts D (fun _ : ℕ => proj) proj :=
    mapCInfConvergence_const proj
  have hfirst_convergence : MapCInfConvergenceOnCompacts D
      (fun n q => v n q.1 q.2.1) (fun q => vInf q.1 q.2.1) := by
    simpa only [proj] using
      (MapCInfConvergenceOnCompacts.comp
        (U := D) (V := Ω) (B := fun _ : ℕ => proj) (Binf := proj)
        (A := fun n q => v n q.1 q.2) (Ainf := fun q => vInf q.1 q.2)
        hD hΩ hproj_convergence hv_convergence (fun _ => hproj_cd) hproj_cd
        hv_cd hvInf_cd hprojMap (fun _ => hprojMap))
  have hraw_convergence : MapCInfConvergenceOnCompacts Ω
      (fun n q => fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q)
      (fun q => fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q) :=
    MapCInfConvergenceOnCompacts.fderivOn hΩ hv_convergence hv_cd hvInf_cd
  have hraw_cd : ∀ n, ContDiffOn ℝ ∞
      (fun q => fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q) Ω := by
    intro n
    exact (hv_cd n).fderiv_of_isOpen hΩ (by exact_mod_cast le_top)
  have hrawInf_cd : ContDiffOn ℝ ∞
      (fun q => fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q) Ω :=
    hvInf_cd.fderiv_of_isOpen hΩ (by exact_mod_cast le_top)
  let postL : ((ℝ × X) →L[ℝ] X) →L[ℝ] (X →L[ℝ] X) :=
    (ContinuousLinearMap.compL ℝ X (ℝ × X) X).flip
      (ContinuousLinearMap.inr ℝ ℝ X)
  have hpartial_convergence : MapCInfConvergenceOnCompacts Ω
      (fun n q => postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q))
      (fun q => postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q)) :=
    mapCInfConvergence_clm hΩ postL hraw_convergence hraw_cd hrawInf_cd
  have hpartial_cd : ∀ n, ContDiffOn ℝ ∞
      (fun q => postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q)) Ω :=
    fun n => (hraw_cd n).continuousLinearMap_comp postL
  have hpartialInf_cd : ContDiffOn ℝ ∞
      (fun q => postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q)) Ω :=
    hrawInf_cd.continuousLinearMap_comp postL
  have hpartial_proj_convergence : MapCInfConvergenceOnCompacts D
      (fun n q => postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) (proj q)))
      (fun q => postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) (proj q))) := by
    simpa only using
      (MapCInfConvergenceOnCompacts.comp
        (U := D) (V := Ω) (B := fun _ : ℕ => proj) (Binf := proj)
        (A := fun n q => postL
          (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q))
        (Ainf := fun q => postL
          (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q))
        hD hΩ hproj_convergence hpartial_convergence (fun _ => hproj_cd) hproj_cd
        hpartial_cd hpartialInf_cd hprojMap (fun _ => hprojMap))
  let zproj : ℝ × (X × (P →L[ℝ] X)) → (P →L[ℝ] X) := fun q => q.2.2
  have hz_cd : ContDiffOn ℝ ∞ zproj D :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  have hz_convergence : MapCInfConvergenceOnCompacts D (fun _ : ℕ => zproj) zproj :=
    mapCInfConvergence_const zproj
  have hpair_convergence : MapCInfConvergenceOnCompacts D
      (fun n q =>
        (postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) (proj q)), zproj q))
      (fun q =>
        (postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) (proj q)), zproj q)) := by
    apply mapCInfConvergence_prodMk hD hpartial_proj_convergence hz_convergence
    · exact fun n => (hpartial_cd n).comp hproj_cd hprojMap
    · exact hpartialInf_cd.comp hproj_cd hprojMap
    · exact fun _ => hz_cd
    · exact hz_cd
  let compMap : (X →L[ℝ] X) × (P →L[ℝ] X) → (P →L[ℝ] X) :=
    fun q => q.1.comp q.2
  have hcomp_cd : ContDiff ℝ ∞ compMap :=
    (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := P) (F := X) (G := X)).contDiff
  have hsecond_convergence : MapCInfConvergenceOnCompacts D
      (fun n q => compMap
        (postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) (proj q)), zproj q))
      (fun q => compMap
        (postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) (proj q)), zproj q)) := by
    simpa only using
      (MapCInfConvergenceOnCompacts.comp
        (U := D) (V := (Set.univ : Set ((X →L[ℝ] X) × (P →L[ℝ] X))))
        (B := fun n q =>
          (postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) (proj q)), zproj q))
        (Binf := fun q =>
          (postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) (proj q)), zproj q))
        (A := fun _ : ℕ => compMap) (Ainf := compMap)
        hD isOpen_univ hpair_convergence (mapCInfConvergence_const compMap)
        (fun n => ((hpartial_cd n).comp hproj_cd hprojMap).prodMk hz_cd)
        ((hpartialInf_cd.comp hproj_cd hprojMap).prodMk hz_cd)
        (fun _ => hcomp_cd.contDiffOn) hcomp_cd.contDiffOn
        (fun _ _ => mem_univ _) (fun _ _ _ => mem_univ _))
  have hfinal : MapCInfConvergenceOnCompacts D
      (fun n q =>
        (v n q.1 q.2.1,
          compMap
            (postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) (proj q)), zproj q)))
      (fun q =>
        (vInf q.1 q.2.1,
          compMap
            (postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) (proj q)), zproj q))) := by
    apply mapCInfConvergence_prodMk hD hfirst_convergence hsecond_convergence
    · intro n
      exact (hv_cd n).comp hproj_cd hprojMap
    · exact hvInf_cd.comp hproj_cd hprojMap
    · intro n
      exact hcomp_cd.contDiffOn.comp
        (((hpartial_cd n).comp hproj_cd hprojMap).prodMk hz_cd)
        (fun _ _ => mem_univ _)
    · exact hcomp_cd.contDiffOn.comp
        ((hpartialInf_cd.comp hproj_cd hprojMap).prodMk hz_cd)
        (fun _ _ => mem_univ _)
  apply hfinal.congr hD
  · intro n q hq
    have hC1 : ContDiffOn ℝ 1 (uncurry (v n)) Ω :=
      (hv_cd n).of_le (by exact_mod_cast le_top)
    have hpartial := Analysis.ODE.Flow.partial_fderiv_eq_comp_inr_on_open
      hΩ hC1 (proj q) (hprojMap hq)
    change
      (v n q.1 q.2.1, (fderiv ℝ (v n q.1) q.2.1).comp q.2.2) =
        (v n q.1 q.2.1,
          (postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) (proj q))).comp
            (zproj q))
    rw [hpartial]
    rfl
  · intro q hq
    have hC1 : ContDiffOn ℝ 1 (uncurry vInf) Ω :=
      hvInf_cd.of_le (by exact_mod_cast le_top)
    have hpartial := Analysis.ODE.Flow.partial_fderiv_eq_comp_inr_on_open
      hΩ hC1 (proj q) (hprojMap hq)
    change
      (vInf q.1 q.2.1, (fderiv ℝ (vInf q.1) q.2.1).comp q.2.2) =
        (vInf q.1 q.2.1,
          (postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) (proj q))).comp
            (zproj q))
    rw [hpartial]
    rfl

end CheegerGromovCompactness
end DifferentialGeometry

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry.Analysis.ODE.Flow

variable {Q X : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_continuous_spatialJetPrefix_paramTangentVF (n : ℕ) :
    ∃ T : (((i : Fin (n + 2)) → X [×i.val]→L[ℝ] X) × (X × (Q →L[ℝ] X))) →
        ((i : Fin (n + 1)) → (X × (Q →L[ℝ] X)) [×i.val]→L[ℝ] (X × (Q →L[ℝ] X))),
      Continuous T ∧ ∀ v : ℝ → X → X, ∀ t, ContDiff ℝ (n + 1) (v t) → ∀ z,
        T (spatialJetPrefix (n + 1) (v t) z.1, z) =
          spatialJetPrefix n (paramTangentVF Q v t) z := by
  let Y := X × (Q →L[ℝ] X)
  let W := X × ((X →L[ℝ] X) × (Q →L[ℝ] X))
  let A := (i : Fin (n + 2)) → X [×i.val]→L[ℝ] X
  let U (f : X → X) (z : Y) : W := (f z.1, fderiv ℝ f z.1, z.2)
  let R : W → Y := fun w => (w.1, w.2.1.comp w.2.2)
  have hR : ContDiff ℝ ∞ R :=
    contDiff_fst.prodMk
      ((isBoundedBilinearMap_comp (𝕜 := ℝ) (E := Q) (F := X) (G := X)).contDiff.comp
        contDiff_snd)
  let UJet (k : ℕ) (hk : k ≤ n) (p : A × Y) : Y [×k]→L[ℝ] W :=
    ((p.1 ⟨k, by omega⟩).compContinuousLinearMap
      (fun _ : Fin k => ContinuousLinearMap.fst ℝ X (Q →L[ℝ] X))).prod
      ((ContinuousMultilinearMap.compContinuousLinearMap
          ((continuousMultilinearCurryRightEquiv' ℝ k X X) (p.1 ⟨k + 1, by omega⟩))
          (fun _ : Fin k => ContinuousLinearMap.fst ℝ X (Q →L[ℝ] X))).prod
        (iteratedFDeriv ℝ k (fun z : Y => z.2) p.2))
  have hUJet (k : ℕ) (hk : k ≤ n) : Continuous (UJet k hk) := by
    have hfirst : Continuous (fun p : A × Y =>
        (p.1 ⟨k, by omega⟩).compContinuousLinearMap
          (fun _ : Fin k => ContinuousLinearMap.fst ℝ X (Q →L[ℝ] X))) :=
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin k => ContinuousLinearMap.fst ℝ X (Q →L[ℝ] X))).continuous.comp
        ((continuous_apply (⟨k, by omega⟩ : Fin (n + 2))).comp continuous_fst)
    have hsecond : Continuous (fun p : A × Y =>
        ContinuousMultilinearMap.compContinuousLinearMap
          ((continuousMultilinearCurryRightEquiv' ℝ k X X) (p.1 ⟨k + 1, by omega⟩))
            (fun _ : Fin k => ContinuousLinearMap.fst ℝ X (Q →L[ℝ] X))) :=
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin k => ContinuousLinearMap.fst ℝ X (Q →L[ℝ] X))).continuous.comp
        ((continuousMultilinearCurryRightEquiv' ℝ k X X).continuous.comp
          ((continuous_apply (⟨k + 1, by omega⟩ : Fin (n + 2))).comp continuous_fst))
    have hthird : Continuous (fun p : A × Y =>
        iteratedFDeriv ℝ k (fun z : Y => z.2) p.2) :=
      (ContDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)
        (contDiff_snd : ContDiff ℝ ∞ (fun z : Y => z.2))).comp continuous_snd
    exact (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin k => Y) X
      ((X →L[ℝ] X) × (Q →L[ℝ] X))).continuous.comp
      (hfirst.prodMk ((ContinuousMultilinearMap.prodL ℝ (fun _ : Fin k => Y)
        (X →L[ℝ] X) (Q →L[ℝ] X)).continuous.comp (hsecond.prodMk hthird)))
  let U₀ (p : A × Y) : W := continuousMultilinearCurryFin0 ℝ Y W (UJet 0 (Nat.zero_le n) p)
  have hU₀ : Continuous U₀ :=
    (continuousMultilinearCurryFin0 ℝ Y W).continuous.comp (hUJet 0 (Nat.zero_le n))
  let T (p : A × Y) (j : Fin (n + 1)) : Y [×j.val]→L[ℝ] Y :=
    ∑ c : OrderedFinpartition j.val,
      c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length R (U₀ p))
        (fun i => UJet (c.partSize i)
          ((c.partSize_le i).trans (Nat.le_of_lt_succ j.isLt)) p)
  have hT : Continuous T := by
    apply continuous_pi
    intro j
    have hterm (c : OrderedFinpartition j.val) : Continuous (fun p : A × Y =>
        c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length R (U₀ p))
          (fun i => UJet (c.partSize i)
            ((c.partSize_le i).trans (Nat.le_of_lt_succ j.isLt)) p)) := by
      have houter : Continuous (fun p : A × Y =>
          iteratedFDeriv ℝ c.length R (U₀ p)) :=
        (ContDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top) hR).comp hU₀
      have hinner : Continuous (fun p : A × Y =>
          fun i : Fin c.length => UJet (c.partSize i)
            ((c.partSize_le i).trans (Nat.le_of_lt_succ j.isLt)) p) :=
        continuous_pi fun i => hUJet (c.partSize i)
          ((c.partSize_le i).trans (Nat.le_of_lt_succ j.isLt))
      let Lflip : ContinuousMultilinearMap ℝ
          (fun i : Fin c.length => Y [×c.partSize i]→L[ℝ] W)
          ((W [×c.length]→L[ℝ] Y) →L[ℝ] Y [×j.val]→L[ℝ] Y) :=
        (c.compAlongOrderedFinpartitionL ℝ Y W Y).flipMultilinear
      simpa only [Lflip, Function.comp_apply, ContinuousLinearMap.flipMultilinear_apply_apply,
        OrderedFinpartition.compAlongOrderedFinpartitionL_apply] using
        ((ContinuousMultilinearMap.contDiff (𝕜 := ℝ) (n := 0) Lflip).continuous.comp hinner).clm_apply
          houter
    exact continuous_finsetSum _ fun c _ => hterm c
  refine ⟨T, hT, ?_⟩
  intro v t hv z
  have hvn : ContDiff ℝ n (v t) := hv.of_le (by exact_mod_cast Nat.le_succ n)
  have hDv : ContDiff ℝ n (fderiv ℝ (v t)) := hv.fderiv_right (by simp)
  have hfs : ContDiff ℝ n (fun y : Y => v t y.1) := hvn.comp contDiff_fst
  have hdfs : ContDiff ℝ n (fun y : Y => fderiv ℝ (v t) y.1) :=
    hDv.comp contDiff_fst
  have hsnd : ContDiff ℝ n (fun y : Y => y.2) := contDiff_snd
  have hU : ContDiff ℝ n (U (v t)) := hfs.prodMk (hdfs.prodMk hsnd)
  have hRn : ContDiff ℝ n R := hR.of_le (by exact_mod_cast le_top)
  have hUeq (k : ℕ) (hk : k ≤ n) :
      UJet k hk (spatialJetPrefix (n + 1) (v t) z.1, z) =
        iteratedFDeriv ℝ k (U (v t)) z := by
    have hf : iteratedFDeriv ℝ k (fun y : Y => v t y.1) z =
        (iteratedFDeriv ℝ k (v t) z.1).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.fst ℝ X (Q →L[ℝ] X)) :=
      (ContinuousLinearMap.fst ℝ X (Q →L[ℝ] X)).iteratedFDeriv_comp_right hvn z
        (by exact_mod_cast hk)
    have hdf : iteratedFDeriv ℝ k (fun y : Y => fderiv ℝ (v t) y.1) z =
        (iteratedFDeriv ℝ k (fderiv ℝ (v t)) z.1).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.fst ℝ X (Q →L[ℝ] X)) :=
      (ContinuousLinearMap.fst ℝ X (Q →L[ℝ] X)).iteratedFDeriv_comp_right hDv z
        (by exact_mod_cast hk)
    have hcurry : (continuousMultilinearCurryRightEquiv' ℝ k X X)
        (iteratedFDeriv ℝ (k + 1) (v t) z.1) =
          iteratedFDeriv ℝ k (fderiv ℝ (v t)) z.1 := by
      simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        LinearIsometryEquiv.apply_symm_apply]
    change _ = iteratedFDeriv ℝ k
      (fun y : Y => (v t y.1, fderiv ℝ (v t) y.1, y.2)) z
    rw [iteratedFDeriv_prodMk hfs.contDiffAt (hdfs.prodMk hsnd).contDiffAt
      (by exact_mod_cast hk)]
    rw [iteratedFDeriv_prodMk hdfs.contDiffAt hsnd.contDiffAt
      (by exact_mod_cast hk), hf, hdf]
    simp only [UJet, spatialJetPrefix, hcurry]
  have hU₀eq : U₀ (spatialJetPrefix (n + 1) (v t) z.1, z) = U (v t) z := by
    dsimp only [U₀]
    rw [hUeq 0 (Nat.zero_le n)]
    rfl
  funext j
  change T (spatialJetPrefix (n + 1) (v t) z.1, z) j =
    iteratedFDeriv ℝ j.val (paramTangentVF Q v t) z
  have hcompEq : paramTangentVF Q v t = R ∘ U (v t) := by
    funext y
    rfl
  rw [hcompEq]
  dsimp only [T]
  simp only [hU₀eq, hUeq]
  simpa only [FormalMultilinearSeries.taylorComp,
    FormalMultilinearSeries.compAlongOrderedFinpartition, ftaylorSeries, Function.comp_def,
    R, U, paramTangentVF] using
    (iteratedFDeriv_comp hRn.contDiffAt hU.contDiffAt
      (i := j.val) (by exact_mod_cast Nat.le_of_lt_succ j.isLt)).symm

end DifferentialGeometry.Analysis.ODE.Flow

end
