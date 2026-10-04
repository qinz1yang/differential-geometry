import DifferentialGeometry.Analysis.Calculus.MapConvergence.Bilinear
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteComposition
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteRegularity
import DifferentialGeometry.Analysis.Calculus.MapConvergence.EventualCongruence

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

theorem MapCPConvergenceOn.pullbackForm
    {X V W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {K : Set X} {p : ℕ} (hK : IsCompact K)
    {B : ℕ → X → W →L[ℝ] W →L[ℝ] ℝ} {Binf : X → W →L[ℝ] W →L[ℝ] ℝ}
    {D : ℕ → X → V →L[ℝ] W} {Dinf : X → V →L[ℝ] W}
    (hB : MapCPConvergenceOn K p B Binf) (hD : MapCPConvergenceOn K p D Dinf)
    (hBinf : ∀ x ∈ K, ContDiffAt ℝ p Binf x)
    (hDinf : ∀ x ∈ K, ContDiffAt ℝ p Dinf x)
    (hBc : ∀ᶠ i in atTop, ∀ x ∈ K, ContDiffAt ℝ p (B i) x)
    (hDc : ∀ᶠ i in atTop, ∀ x ∈ K, ContDiffAt ℝ p (D i) x) :
    MapCPConvergenceOn K p (fun i x => _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm (B i x, D i x))
      (fun x => _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm (Binf x, Dinf x)) := by
  let : NormedAddCommGroup (W →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (W →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (V →L[ℝ] W) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (V →L[ℝ] W) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (W →L[ℝ] W →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (W →L[ℝ] W →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (V →L[ℝ] W →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (V →L[ℝ] W →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let C : (W →L[ℝ] W →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] W) →L[ℝ]
      V →L[ℝ] W →L[ℝ] ℝ := ContinuousLinearMap.compL ℝ V W (W →L[ℝ] ℝ)
  have hBD := MapCPConvergenceOn.bilinear
    (E := X) (F := W →L[ℝ] W →L[ℝ] ℝ) (G := V →L[ℝ] W)
    (H := V →L[ℝ] W →L[ℝ] ℝ) C hK hB hD hBinf hDinf hBc hDc
  have hCc : ContDiff ℝ p C := C.contDiff
  have hBDinf : ∀ x ∈ K, ContDiffAt ℝ p
      (fun y => C (Binf y) (Dinf y)) x := by
    intro x hx
    exact (hCc.contDiffAt.comp x (hBinf x hx)).clm_apply (hDinf x hx)
  have hBDc : ∀ᶠ i in atTop, ∀ x ∈ K,
      ContDiffAt ℝ p (fun y => C (B i y) (D i y)) x := by
    filter_upwards [hBc, hDc] with i hi hiD x hx
    exact (hCc.contDiffAt.comp x (hi x hx)).clm_apply (hiD x hx)
  let L : (V →L[ℝ] W) →L[ℝ] (V →L[ℝ] W →L[ℝ] ℝ) →L[ℝ]
      V →L[ℝ] V →L[ℝ] ℝ :=
    ContinuousLinearMap.precompR V (ContinuousLinearMap.compL ℝ V W ℝ).flip
  have heq (b : W →L[ℝ] W →L[ℝ] ℝ) (d : V →L[ℝ] W) :
      L d (C b d) = _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm (b, d) := by
    ext v w
    rfl
  have hresult := MapCPConvergenceOn.bilinear
    (E := X) (F := V →L[ℝ] W) (G := V →L[ℝ] W →L[ℝ] ℝ)
    (H := V →L[ℝ] V →L[ℝ] ℝ) L hK hD hBD hDinf hBDinf hDc hBDc
  have hseq : (fun i x => L (D i x) (C (B i x) (D i x))) =
      (fun i x => _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm (B i x, D i x)) := by
    funext i x
    exact heq _ _
  have hlim : (fun x => L (Dinf x) (C (Binf x) (Dinf x))) =
      (fun x => _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm (Binf x, Dinf x)) := by
    funext x
    exact heq _ _
  rw [hseq, hlim] at hresult
  exact hresult

theorem mapCPConvergenceOn_pullbackForm_comp_fderiv_locally
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
    {U K : Set E} {V : Set F} {p : ℕ} (hV : IsOpen V) (hK : IsCompact K)
    {A : ℕ → E → F} {Ainf : E → F}
    {B : ℕ → F → F →L[ℝ] F →L[ℝ] ℝ} {Binf : F → F →L[ℝ] F →L[ℝ] ℝ}
    (hA : MapCPConvergenceOn K (p + 1) A Ainf)
    (hB : ∀ S : Set F, IsCompact S → S ⊆ V → MapCPConvergenceOn S p B Binf)
    (hAc : ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
        ∀ᶠ i in atTop, ContDiffOn ℝ (p + 1 : ℕ) (A i) W ∧ MapsTo (A i) W V)
    (hAinf : ContDiffOn ℝ (p + 1 : ℕ) Ainf U)
    (hBc : ∀ i, ContDiffOn ℝ p (B i) V)
    (hBinf : ContDiffOn ℝ p Binf V)
    (hmap : MapsTo Ainf U V) :
    MapCPConvergenceOn K p
      (fun i x => pullbackForm (B i (A i x), fderiv ℝ (A i) x))
      (fun x => pullbackForm (Binf (Ainf x), fderiv ℝ Ainf x)) := by
  classical
  obtain ⟨W, hW, hKW, hWU, heventually⟩ := hAc
  obtain ⟨N, hN⟩ := eventually_atTop.mp heventually
  let A' : ℕ → E → F := fun i => if N ≤ i then A i else Ainf
  have hAeq : ∀ᶠ i in atTop, EqOn (A' i) (A i) W := by
    filter_upwards [eventually_ge_atTop N] with i hi
    intro x _
    simp only [A', ite_eq_left hi]
  have hA'c : ∀ i, ContDiffOn ℝ (p + 1 : ℕ) (A' i) W := by
    intro i
    by_cases hi : N ≤ i
    · simpa only [A', ite_eq_left hi] using (hN i hi).1
    · simpa only [A', ite_eq_right hi] using hAinf.mono hWU
  have hA'map : ∀ i, MapsTo (A' i) W V := by
    intro i
    by_cases hi : N ≤ i
    · simpa only [A', ite_eq_left hi] using (hN i hi).2
    · simpa only [A', ite_eq_right hi] using hmap.mono_left hWU
  have hA' : MapCPConvergenceOn K (p + 1) A' Ainf :=
    hA.congr_eventually hW hKW hAeq (Set.eqOn_refl _ _)
  have hp : (p : ℕ∞ω) ≤ (p + 1 : ℕ) := by exact_mod_cast Nat.le_succ p
  have hBA : MapCPConvergenceOn K p (fun i x => B i (A' i x))
      (fun x => Binf (Ainf x)) :=
    (hA'.mono_order (Nat.le_succ p)).comp_finite hW hV hK hKW hB
      (fun i => (hA'c i).of_le hp) ((hAinf.mono hWU).of_le hp)
      hBc hBinf (hmap.mono_left hWU) hA'map
  have hDA : MapCPConvergenceOn K p (fun i => fderiv ℝ (A' i)) (fderiv ℝ Ainf) :=
    hA'.fderiv
      (Eventually.of_forall fun i x hx =>
        ((hA'c i).differentiableOn (by simp)).eventually_differentiableAt
          (hW.mem_nhds (hKW hx)))
      (fun x hx => ((hAinf.mono hWU).differentiableOn (by simp)).eventually_differentiableAt
        (hW.mem_nhds (hKW hx)))
  have hBAc : ∀ i, ContDiffOn ℝ p (fun x => B i (A' i x)) W := by
    intro i
    simpa only [Function.comp_def] using
      (hBc i).comp ((hA'c i).of_le hp) (hA'map i)
  have hBAinf : ContDiffOn ℝ p (fun x => Binf (Ainf x)) W := by
    simpa only [Function.comp_def] using
      hBinf.comp ((hAinf.mono hWU).of_le hp) (hmap.mono_left hWU)
  have hP := MapCPConvergenceOn.pullbackForm hK hBA hDA
    (fun x hx => hBAinf.contDiffAt (hW.mem_nhds (hKW hx)))
    (fun x hx => ((hAinf.mono hWU).contDiffAt
      (hW.mem_nhds (hKW hx))).fderiv_right (m := p) (by simp))
    (Eventually.of_forall fun i x hx => (hBAc i).contDiffAt (hW.mem_nhds (hKW hx)))
    (Eventually.of_forall fun i x hx =>
      ((hA'c i).contDiffAt (hW.mem_nhds (hKW hx))).fderiv_right (m := p) (by simp))
  apply hP.congr_eventually hW hKW ?_ (Set.eqOn_refl _ _)
  filter_upwards [eventually_ge_atTop N] with i hi
  intro x _
  simp only [A', ite_eq_left hi]

end DifferentialGeometry.CheegerGromovCompactness
