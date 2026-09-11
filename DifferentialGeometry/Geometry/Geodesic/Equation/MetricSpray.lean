import DifferentialGeometry.Geometry.Geodesic.Equation.Koszul
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import Mathlib.Analysis.Calculus.FDeriv.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace MetricKoszul
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [ContinuousDualEquiv E]
noncomputable local instance sprayDualNormedGroup :
    NormedAddCommGroup (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance sprayDualNormedSpace :
    NormedSpace Real (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance sprayBilinNormedGroup :
    NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance sprayBilinNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance sprayEndoNormedGroup :
    NormedAddCommGroup (E →L[Real] E) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance sprayEndoNormedSpace :
    NormedSpace Real (E →L[Real] E) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance sprayVecBilinNormedGroup :
    NormedAddCommGroup (E →L[Real] E →L[Real] E) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance sprayVecBilinNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] E) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance sprayTriNormedGroup :
    NormedAddCommGroup (E →L[Real] E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance sprayTriNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance sprayDualFiniteDim
    [FiniteDimensional Real E] : FiniteDimensional Real (E →L[Real] Real) :=
  ContinuousLinearMap.finiteDimensional

noncomputable local instance sprayBilinFiniteDim
    [FiniteDimensional Real E] :
    FiniteDimensional Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.finiteDimensional

noncomputable local instance sprayEndoFiniteDim
    [FiniteDimensional Real E] : FiniteDimensional Real (E →L[Real] E) :=
  ContinuousLinearMap.finiteDimensional

noncomputable local instance sprayVecBilinFiniteDim
    [FiniteDimensional Real E] :
    FiniteDimensional Real (E →L[Real] E →L[Real] E) :=
  ContinuousLinearMap.finiteDimensional

noncomputable local instance sprayTriFiniteDim
    [FiniteDimensional Real E] :
    FiniteDimensional Real (E →L[Real] E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.finiteDimensional

private noncomputable def koszulRieszOp :
    (E →L[Real] E →L[Real] E →L[Real] Real) →L[Real]
      (E →L[Real] E →L[Real] E) :=
  (ContinuousLinearMap.compL Real E
      (E →L[Real] E →L[Real] Real) (E →L[Real] E)
      (ContinuousLinearMap.compL Real E (E →L[Real] Real) E
        (ContinuousDualEquiv.equiv (E := E)).symm.toContinuousLinearMap)).comp
    koszulCovCLM

@[simp] private theorem koszulRieszOp_apply
    (D : E →L[Real] E →L[Real] E →L[Real] Real) (u v : E) :
    koszulRieszOp D u v =
      (ContinuousDualEquiv.equiv (E := E)).symm (koszulCov D u v) := by
  simp [koszulRieszOp]

private noncomputable def postBilin :
    (E →L[Real] E) →L[Real]
      (E →L[Real] E →L[Real] E) →L[Real]
        (E →L[Real] E →L[Real] E) :=
  (ContinuousLinearMap.compL Real E (E →L[Real] E) (E →L[Real] E)).comp
    (ContinuousLinearMap.compL Real E E E)

private noncomputable def gramCLM :
    (E →L[Real] E →L[Real] Real) →L[Real] (E →L[Real] E) :=
  ContinuousLinearMap.compL Real E (E →L[Real] Real) E
    (ContinuousDualEquiv.equiv (E := E)).symm.toContinuousLinearMap

@[simp] private theorem gramCLM_apply
    (B : E →L[Real] E →L[Real] Real) :
    gramCLM B =
      (ContinuousDualEquiv.equiv (E := E)).symm.toContinuousLinearMap.comp B := by
  rfl

private theorem gramCLM_isUnit
    [CompleteSpace E] [CoerciveBilinInverse E]
    {B : E →L[Real] E →L[Real] Real} (hB : IsCoercive B) :
    IsUnit (gramCLM B) := by
  let eB : E ≃L[Real] (E →L[Real] Real) :=
    ContinuousLinearEquiv.ofBijective B
      (LinearMap.ker_eq_bot.mpr hB.bilin_injective)
      (LinearMap.range_eq_top.mpr (CoerciveBilinInverse.surjective hB))
  let e : E ≃L[Real] E := eB.trans (ContinuousDualEquiv.equiv (E := E)).symm
  refine ⟨e.toUnit, ?_⟩
  change (ContinuousDualEquiv.equiv (E := E)).symm.toContinuousLinearMap.comp B =
    gramCLM B
  rfl

noncomputable def raisedKoszulOp
    (B : E →L[Real] E →L[Real] Real)
    (D : E →L[Real] E →L[Real] E →L[Real] Real) :
    E →L[Real] E →L[Real] E :=
  postBilin
    (Ring.inverse (gramCLM B))
    (koszulRieszOp D)

@[simp] theorem raisedKoszulOp_apply
    (B : E →L[Real] E →L[Real] Real)
    (D : E →L[Real] E →L[Real] E →L[Real] Real) (u v : E) :
    raisedKoszulOp B D u v =
      Ring.inverse (gramCLM B)
        ((ContinuousDualEquiv.equiv (E := E)).symm (koszulCov D u v)) := by
  rfl

theorem raisedKoszulOp_eq
    [CompleteSpace E] [CoerciveBilinInverse E]
    {B : E →L[Real] E →L[Real] Real} (hB : IsCoercive B)
    (D : E →L[Real] E →L[Real] E →L[Real] Real) (u v : E) :
    raisedKoszulOp B D u v = koszulVec hB D u v := by
  rw [raisedKoszulOp_apply]
  let eB : E ≃L[Real] (E →L[Real] Real) :=
    ContinuousLinearEquiv.ofBijective B
      (LinearMap.ker_eq_bot.mpr hB.bilin_injective)
      (LinearMap.range_eq_top.mpr (CoerciveBilinInverse.surjective hB))
  let e : E ≃L[Real] E := eB.trans (ContinuousDualEquiv.equiv (E := E)).symm
  change Ring.inverse (↑e.toUnit : E →L[Real] E)
      ((ContinuousDualEquiv.equiv (E := E)).symm (koszulCov D u v)) = _
  rw [Ring.inverse_unit]
  apply hB.bilin_injective
  rw [apply_koszul_vec]
  have he := e.apply_symm_apply
    ((ContinuousDualEquiv.equiv (E := E)).symm (koszulCov D u v))
  change (ContinuousDualEquiv.equiv (E := E)).symm
      (B (e.symm ((ContinuousDualEquiv.equiv (E := E)).symm (koszulCov D u v)))) =
    (ContinuousDualEquiv.equiv (E := E)).symm (koszulCov D u v) at he
  exact (ContinuousDualEquiv.equiv (E := E)).symm.injective he

noncomputable def metricSpray
    (g : E → E →L[Real] E →L[Real] Real) (z : E × E) : E × E :=
  (z.2, -raisedKoszulOp (g z.1) (fderiv Real g z.1) z.2 z.2)

theorem metricSpray_eq
    [CompleteSpace E] [CoerciveBilinInverse E]
    (g : E → E →L[Real] E →L[Real] Real) (z : E × E)
    (hg : IsCoercive (g z.1)) :
    metricSpray g z =
      (z.2, -koszulVec hg (fderiv Real g z.1) z.2 z.2) := by
  rw [metricSpray, raisedKoszulOp_eq hg]

open DifferentialGeometry.Analysis
open DifferentialGeometry.CheegerGromovCompactness
open scoped ContDiff

private theorem invGram_smooth
    [FiniteDimensional Real E]
    {U : Set E}
    {g : E → E →L[Real] E →L[Real] Real}
    (hg_cd : ContDiffOn Real (∞ : WithTop ℕ∞) g U)
    (hg_co : ∀ x, x ∈ U → IsCoercive (g x)) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun x => Ring.inverse (gramCLM (g x))) U := by
  have hgram : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun x => gramCLM (g x)) U := by
    simpa [Function.comp_def] using gramCLM.contDiff.comp_contDiffOn hg_cd
  exact ContDiffOn.comp
    (contDiffOn_ringInverse (R := E →L[Real] E) (𝕜 := Real)
      (∞ : WithTop ℕ∞)) hgram (fun x hx => gramCLM_isUnit (hg_co x hx))

private theorem invGram_convergence
    [FiniteDimensional Real E]
    {U : Set E} (hU : IsOpen U)
    {g : ℕ → E → E →L[Real] E →L[Real] Real}
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hg_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (g n) U)
    (hgInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) gInf U)
    (hg_co : ∀ n x, x ∈ U → IsCoercive (g n x))
    (hgInf_co : ∀ x, x ∈ U → IsCoercive (gInf x))
    (hg_convergence : MapCInfConvergenceOnCompacts U g gInf) :
    MapCInfConvergenceOnCompacts U
      (fun n x => Ring.inverse (gramCLM (g n x)))
      (fun x => Ring.inverse (gramCLM (gInf x))) := by
  let : ProperSpace (E →L[Real] E) := FiniteDimensional.proper Real _
  have hgram_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun x => gramCLM (g n x)) U := fun n => by
    simpa [Function.comp_def] using gramCLM.contDiff.comp_contDiffOn (hg_cd n)
  have hgramInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun x => gramCLM (gInf x)) U := by
    simpa [Function.comp_def] using gramCLM.contDiff.comp_contDiffOn hgInf_cd
  have hgram_convergence : MapCInfConvergenceOnCompacts U
      (fun n x => gramCLM (g n x)) (fun x => gramCLM (gInf x)) :=
    mapCInfConvergence_clm (E' := E)
      (F' := E →L[Real] E →L[Real] Real) (G' := E →L[Real] E)
      hU (gramCLM (E := E)) hg_convergence hg_cd hgInf_cd
  exact MapCInfConvergenceOnCompacts.ringInv (E := E) (R := E →L[Real] E)
    hU hgram_convergence hgram_cd hgramInf_cd
    (fun n x hx => gramCLM_isUnit (hg_co n x hx))
    (fun x hx => gramCLM_isUnit (hgInf_co x hx))

private theorem koszulRiesz_smooth
    {U : Set E} (hU : IsOpen U)
    {g : E → E →L[Real] E →L[Real] Real}
    (hg_cd : ContDiffOn Real (∞ : WithTop ℕ∞) g U) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun x => koszulRieszOp (fderiv Real g x)) U := by
  exact (koszulRieszOp (E := E)).contDiff.comp_contDiffOn
    (hg_cd.fderiv_of_isOpen hU
      (by rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]))

private theorem koszulRiesz_convergence
    {U : Set E} (hU : IsOpen U)
    {g : ℕ → E → E →L[Real] E →L[Real] Real}
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hg_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (g n) U)
    (hgInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) gInf U)
    (hg_convergence : MapCInfConvergenceOnCompacts U g gInf) :
    MapCInfConvergenceOnCompacts U
      (fun n x => koszulRieszOp (fderiv Real (g n) x))
      (fun x => koszulRieszOp (fderiv Real gInf x)) := by
  have hderiv : MapCInfConvergenceOnCompacts U
      (fun n x => fderiv Real (g n) x) (fun x => fderiv Real gInf x) :=
    MapCInfConvergenceOnCompacts.fderivOn (E := E)
      (F := E →L[Real] E →L[Real] Real) hU hg_convergence hg_cd hgInf_cd
  exact mapCInfConvergence_clm (E' := E)
    (F' := E →L[Real] E →L[Real] E →L[Real] Real)
    (G' := E →L[Real] E →L[Real] E)
    hU (koszulRieszOp (E := E)) hderiv
    (fun n => (hg_cd n).fderiv_of_isOpen hU
      (by rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]))
    (hgInf_cd.fderiv_of_isOpen hU
      (by rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]))

theorem raisedOp_smooth
    [FiniteDimensional Real E]
    {U : Set E} (hU : IsOpen U)
    {g : E → E →L[Real] E →L[Real] Real}
    (hg_cd : ContDiffOn Real (∞ : WithTop ℕ∞) g U)
    (hg_co : ∀ x, x ∈ U → IsCoercive (g x)) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun x => raisedKoszulOp (g x) (fderiv Real g x)) U := by
  simpa [raisedKoszulOp] using
    (postBilin (E := E)).isBoundedBilinearMap.contDiff.comp₂_contDiffOn
      (invGram_smooth hg_cd hg_co) (koszulRiesz_smooth hU hg_cd)

theorem raisedKoszulOp_convergence
    [FiniteDimensional Real E]
    {U : Set E} (hU : IsOpen U)
    {g : ℕ → E → E →L[Real] E →L[Real] Real}
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hg_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (g n) U)
    (hgInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) gInf U)
    (hg_co : ∀ n x, x ∈ U → IsCoercive (g n x))
    (hgInf_co : ∀ x, x ∈ U → IsCoercive (gInf x))
    (hg_convergence : MapCInfConvergenceOnCompacts U g gInf) :
    MapCInfConvergenceOnCompacts U
      (fun n x => raisedKoszulOp (g n x) (fderiv Real (g n) x))
      (fun x => raisedKoszulOp (gInf x) (fderiv Real gInf x)) := by
  let : ProperSpace
      ((E →L[Real] E) × (E →L[Real] E →L[Real] E)) :=
    FiniteDimensional.proper Real _
  have hinv := invGram_convergence hU hg_cd hgInf_cd hg_co hgInf_co hg_convergence
  have hkoszul := koszulRiesz_convergence hU hg_cd hgInf_cd hg_convergence
  have hinv_cd := fun n => invGram_smooth (hg_cd n) (hg_co n)
  have hinvInf_cd := invGram_smooth hgInf_cd hgInf_co
  have hkoszul_cd := fun n => koszulRiesz_smooth hU (hg_cd n)
  have hkoszulInf_cd := koszulRiesz_smooth hU hgInf_cd
  have hpair := mapCInfConvergence_prodMk hU hinv hkoszul hinv_cd hinvInf_cd
    hkoszul_cd hkoszulInf_cd
  let postEval : (E →L[Real] E) × (E →L[Real] E →L[Real] E) →
      E →L[Real] E →L[Real] E := fun q => postBilin (E := E) q.1 q.2
  have hpost : ContDiff Real (∞ : WithTop ℕ∞) postEval :=
    (postBilin (E := E)).isBoundedBilinearMap.contDiff
  simpa [raisedKoszulOp, postEval] using
    (MapCInfConvergenceOnCompacts.comp hU isOpen_univ hpair
      (mapCInfConvergence_const (U := Set.univ) postEval)
      (fun n => (hinv_cd n).prodMk (hkoszul_cd n))
      (hinvInf_cd.prodMk hkoszulInf_cd)
      (fun _ => hpost.contDiffOn) hpost.contDiffOn
      (fun _ _ => Set.mem_univ _) (fun _ _ _ => Set.mem_univ _))

omit [ContinuousDualEquiv E] in
private theorem raisedDiag_convergence
    [FiniteDimensional Real E]
    {U : Set E} (hU : IsOpen U)
    {R : ℕ → E → E →L[Real] E →L[Real] E}
    {RInf : E → E →L[Real] E →L[Real] E}
    (hR_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (R n) U)
    (hRInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) RInf U)
    (hR_convergence : MapCInfConvergenceOnCompacts U R RInf) :
    MapCInfConvergenceOnCompacts (U ×ˢ Set.univ)
      (fun n q => R n q.1 q.2 q.2) (fun q => RInf q.1 q.2 q.2) := by
  let : ProperSpace E := FiniteDimensional.proper Real _
  let : ProperSpace ((E →L[Real] E →L[Real] E) × E) :=
    FiniteDimensional.proper Real _
  let phaseU : Set (E × E) := U ×ˢ Set.univ
  have hphaseU : IsOpen phaseU := hU.prod isOpen_univ
  let fstMap : E × E → E := fun q => q.1
  have hfst : MapCInfConvergenceOnCompacts phaseU (fun _ : ℕ => fstMap) fstMap :=
    mapCInfConvergence_const fstMap
  have hRphase : MapCInfConvergenceOnCompacts phaseU
      (fun n q => R n q.1) (fun q => RInf q.1) := by
    simpa [fstMap] using
      (MapCInfConvergenceOnCompacts.comp hphaseU hU hfst hR_convergence
        (fun _ => contDiff_fst.contDiffOn) contDiff_fst.contDiffOn
        hR_cd hRInf_cd (fun q hq => hq.1) (fun _ q hq => hq.1))
  have hRphase_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun q : E × E => R n q.1) phaseU :=
    fun n => ContDiffOn.comp (hR_cd n) contDiff_fst.contDiffOn (fun q hq => hq.1)
  have hRphaseInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun q : E × E => RInf q.1) phaseU :=
    ContDiffOn.comp hRInf_cd contDiff_fst.contDiffOn (fun q hq => hq.1)
  let sndMap : E × E → E := fun q => q.2
  have hsnd : MapCInfConvergenceOnCompacts phaseU (fun _ : ℕ => sndMap) sndMap :=
    mapCInfConvergence_const sndMap
  have hpair := mapCInfConvergence_prodMk hphaseU hRphase hsnd hRphase_cd
    hRphaseInf_cd (fun _ => contDiff_snd.contDiffOn) contDiff_snd.contDiffOn
  let diagEval : (E →L[Real] E →L[Real] E) × E → E :=
    fun q => q.1 q.2 q.2
  have hdiag : ContDiff Real (∞ : WithTop ℕ∞) diagEval :=
    (contDiff_fst.clm_apply contDiff_snd).clm_apply contDiff_snd
  simpa [phaseU, sndMap, diagEval] using
    (MapCInfConvergenceOnCompacts.comp hphaseU isOpen_univ hpair
      (mapCInfConvergence_const (U := Set.univ) diagEval)
      (fun n => (hRphase_cd n).prodMk contDiff_snd.contDiffOn)
      (hRphaseInf_cd.prodMk contDiff_snd.contDiffOn)
      (fun _ => hdiag.contDiffOn) hdiag.contDiffOn
      (fun _ _ => Set.mem_univ _) (fun _ _ _ => Set.mem_univ _))

theorem metricSpray_contDiffOn
    [FiniteDimensional Real E]
    {U : Set E} (hU : IsOpen U)
    {g : E → E →L[Real] E →L[Real] Real}
    (hg_cd : ContDiffOn Real (∞ : WithTop ℕ∞) g U)
    (hg_co : ∀ x, x ∈ U → IsCoercive (g x)) :
    ContDiffOn Real (∞ : WithTop ℕ∞) (metricSpray g) (U ×ˢ Set.univ) := by
  let R : E → E →L[Real] E →L[Real] E :=
    fun x => raisedKoszulOp (g x) (fderiv Real g x)
  have hR : ContDiffOn Real (∞ : WithTop ℕ∞) R U :=
    raisedOp_smooth hU hg_cd hg_co
  have hdiag : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun q : E × E => R q.1 q.2 q.2) (U ×ˢ Set.univ) :=
    (((hR.comp contDiffOn_fst (fun q hq => hq.1)).clm_apply
      contDiffOn_snd).clm_apply contDiffOn_snd)
  change ContDiffOn Real (∞ : WithTop ℕ∞)
    (fun q : E × E => (q.2, -raisedKoszulOp (g q.1) (fderiv Real g q.1) q.2 q.2))
    (U ×ˢ Set.univ)
  exact contDiffOn_snd.prodMk hdiag.neg

theorem metricSpray_convergence
    [FiniteDimensional Real E]
    {U : Set E} (hU : IsOpen U)
    {g : ℕ → E → E →L[Real] E →L[Real] Real}
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hg_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (g n) U)
    (hgInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) gInf U)
    (hg_co : ∀ n x, x ∈ U → IsCoercive (g n x))
    (hgInf_co : ∀ x, x ∈ U → IsCoercive (gInf x))
    (hg_convergence : MapCInfConvergenceOnCompacts U g gInf) :
    MapCInfConvergenceOnCompacts (U ×ˢ Set.univ)
      (fun n => metricSpray (g n)) (metricSpray gInf) := by
  let R : ℕ → E → E →L[Real] E →L[Real] E :=
    fun n x => raisedKoszulOp (g n x) (fderiv Real (g n) x)
  let RInf : E → E →L[Real] E →L[Real] E :=
    fun x => raisedKoszulOp (gInf x) (fderiv Real gInf x)
  have hR_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (R n) U :=
    fun n => raisedOp_smooth hU (hg_cd n) (hg_co n)
  have hRInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) RInf U :=
    raisedOp_smooth hU hgInf_cd hgInf_co
  have hR_convergence : MapCInfConvergenceOnCompacts U R RInf :=
    raisedKoszulOp_convergence hU hg_cd hgInf_cd hg_co hgInf_co hg_convergence
  have hdiag := raisedDiag_convergence hU hR_cd hRInf_cd hR_convergence
  have hdiag_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun q : E × E => R n q.1 q.2 q.2) (U ×ˢ Set.univ) :=
    fun n => ((((hR_cd n).comp contDiffOn_fst (fun q hq => hq.1)).clm_apply
      contDiffOn_snd).clm_apply contDiffOn_snd)
  have hdiagInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun q : E × E => RInf q.1 q.2 q.2) (U ×ˢ Set.univ) :=
    (((hRInf_cd.comp contDiffOn_fst (fun q hq => hq.1)).clm_apply
      contDiffOn_snd).clm_apply contDiffOn_snd)
  let negCLM : E →L[Real] E := -(ContinuousLinearMap.id Real E)
  have hneg := mapCInfConvergence_clm (hU.prod isOpen_univ) negCLM hdiag
    hdiag_cd hdiagInf_cd
  have hneg_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun q : E × E => negCLM (R n q.1 q.2 q.2)) (U ×ˢ Set.univ) :=
    fun n => negCLM.contDiff.comp_contDiffOn (hdiag_cd n)
  have hnegInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun q : E × E => negCLM (RInf q.1 q.2 q.2)) (U ×ˢ Set.univ) :=
    negCLM.contDiff.comp_contDiffOn hdiagInf_cd
  have hmain := mapCInfConvergence_prodMk (hU.prod isOpen_univ)
    (mapCInfConvergence_const (U := U ×ˢ Set.univ) (fun q : E × E => q.2)) hneg
    (fun _ => contDiffOn_snd) contDiffOn_snd hneg_cd hnegInf_cd
  change MapCInfConvergenceOnCompacts (U ×ˢ Set.univ)
    (fun n q => (q.2, -raisedKoszulOp (g n q.1) (fderiv Real (g n) q.1) q.2 q.2))
    (fun q => (q.2, -raisedKoszulOp (gInf q.1) (fderiv Real gInf q.1) q.2 q.2)) at hmain
  exact hmain

end MetricKoszul
end DifferentialGeometry
