import DifferentialGeometry.Topology.Ehresmann.SideBoundaryIntervalPreserving
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts
import DifferentialGeometry.Topology.Manifold.OpenTarget

/-!
# FC39 GROUP G, RIMBOX R4/R5 (route B): the flow handle kernel (RB-H)

External draft 58 §三 R4–R5, disposition D58-4, route note `build-logs/resume/sheet-FC39-G-RIMBOX.md`
§0 and §3 K3 (lane FC39-G-RIMBOX). On a boundaryless 3-manifold `Y` let `P` (the axial coordinate of
an interval component, `P = φ ∘ proj`) and `B` (`level − height`) satisfy the hypotheses of the
side-boundary transport (`exists_sideBoundary_interval_trivialization_preserving`,
`Topology/Ehresmann/SideBoundaryIntervalPreserving.lean`), and let `D : ClosedCell 2 → Y` be a smooth
injective immersion onto the end fibre `{P = 0, B ≥ 0}`. Then the map
`Hm (w, t) = Fl_t (D w)` (the transport flow applied to the end disk) is a smooth injective immersion
of `ClosedCell 2 × [0, 1]` onto `{P ∈ [0, 1], B ≥ 0}` with `P ∘ Hm = t`, equal to `D` on the first end,
which keeps `B` on the collar `{B < r'}` of every slice; the flow (with the group law, `P ∘ Fl_t = P + t`
on the end slice also beyond the wall, `B` preserved on `{|B| < r'}`) is exported for the rim charts.

* `exists_flowHandle_GRIM` — the kernel (consumer: `FC39GRimFlowHandleApplications.lean`,
  `exists_flowHandle_polar_GRIM`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskCharts_GRIM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_GRIM : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

variable {E H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [T2Space Y] [SigmaCompactSpace Y]

/-- **The flow handle (RB-H kernel).** The transport flow of the side-boundary trivialization
applied to an immersed end disk is a smooth injective immersion of `D² × [0, 1]` onto
`{P ∈ [0, 1], B ≥ 0}` with `P (Hm (w, t)) = t`; the flow is exported. -/
theorem exists_flowHandle_GRIM (hdim : Module.finrank ℝ E = 1 + 1 + Module.finrank ℝ ℝ)
    {P B : Y → ℝ} (hP : ContMDiff I 𝓘(ℝ, ℝ) ∞ P) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B) {a b : ℝ}
    (hreg : ∀ y, P y ∈ Ioo a b → 0 ≤ B y → Surjective (mfderiv I 𝓘(ℝ, ℝ) P y))
    (hregb : ∀ y, P y ∈ Ioo a b → B y = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => (P y, B y)) y))
    (hprop : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo a b → IsCompact (P ⁻¹' K ∩ {y | 0 ≤ B y}))
    {a₀ b₀ : ℝ} (ha₀ : a < a₀) (ha₀0 : a₀ < 0) (hb₀1 : 1 < b₀) (hb₀ : b₀ < b)
    (D : ClosedCell 2 → Y) (hD : ContMDiff (𝓡∂ 2) I ∞ D) (hDinj : Injective D)
    (hDimm : ∀ w, Injective (mfderiv (𝓡∂ 2) I D w))
    (hDr : range D = {y | P y = 0 ∧ 0 ≤ B y}) :
    ∃ Hm : ClosedCell 2 × Icc (0 : ℝ) 1 → Y,
      ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) I ∞ Hm ∧ Injective Hm ∧
      (∀ p, Injective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) I Hm p)) ∧
      (∀ p, P (Hm p) = p.2 ∧ 0 ≤ B (Hm p)) ∧
      range Hm = {y | P y ∈ Icc 0 1 ∧ 0 ≤ B y} ∧
      (∀ w, Hm (w, iccEnd false) = D w) ∧
      ∃ r' : ℝ, 0 < r' ∧ (∀ p, B (D p.1) < r' → B (Hm p) = B (D p.1)) ∧
        ∃ (U : TopologicalSpace.Opens Y) (Fl : ℝ → U ≃ₘ⟮I, I⟯ U),
          ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × U => Fl q.1 q.2) ∧
          Fl 0 = Diffeomorph.refl I U ∞ ∧
          (∀ s t, (Fl s).trans (Fl t) = Fl (s + t)) ∧
          (∀ w, D w ∈ U) ∧
          (∀ p, ∃ hp : D p.1 ∈ U, Hm p = (Fl (p.2 : ℝ) ⟨D p.1, hp⟩ : Y)) ∧
          (∀ z : U, P z = 0 → -r' ≤ B z → ∀ t ∈ Ioo a₀ b₀, P (Fl t z) = t) ∧
          ∀ (z : U) (t : ℝ), |B z| < r' → B (Fl t z) = B z := by
  have h0 : (0 : ℝ) ∈ Ioo a₀ b₀ := ⟨ha₀0, by linarith⟩
  obtain ⟨Θ, -, hΘP, -, -, ⟨r', hr', hΘB, U, hU, Fl, hFl, hFl0, hFlgrp, hΘFl, hFlP, hFlB⟩, O, -,
    hOmem, R, -, hRΘ⟩ :=
    exists_sideBoundary_interval_trivialization_preserving hdim hP hB hreg hregb hprop ha₀ h0 hb₀
  let U' : TopologicalSpace.Opens Y := ⟨U, hU⟩
  have hF0 : ∀ w, P (D w) = 0 ∧ 0 ≤ B (D w) := fun w => by
    have h := mem_range_self (f := D) w
    rw [hDr] at h
    exact h
  have hDU : ∀ w, D w ∈ U := fun w => (hΘFl (⟨D w, hF0 w⟩, ⟨0, h0⟩)).1
  have hIcc : ∀ t : Icc (0 : ℝ) 1, (t : ℝ) ∈ Ioo a₀ b₀ := fun t =>
    ⟨by linarith [t.2.1], by linarith [t.2.2]⟩
  let D' : ClosedCell 2 → U' := fun w => ⟨D w, hDU w⟩
  let Hm : ClosedCell 2 × Icc (0 : ℝ) 1 → Y := fun p => (Fl (p.2 : ℝ) (D' p.1) : Y)
  have hHmΘ : ∀ p : ClosedCell 2 × Icc (0 : ℝ) 1,
      Hm p = Θ (⟨D p.1, hF0 p.1⟩, ⟨p.2, hIcc p.2⟩) := fun p =>
    (hΘFl (⟨D p.1, hF0 p.1⟩, ⟨p.2, hIcc p.2⟩)).2.symm
  have hPHm : ∀ p : ClosedCell 2 × Icc (0 : ℝ) 1, P (Hm p) = p.2 := fun p =>
    hFlP (D' p.1) (hF0 p.1).1 (by linarith [(hF0 p.1).2]) p.2 (hIcc p.2)
  have hBHm : ∀ p : ClosedCell 2 × Icc (0 : ℝ) 1, 0 ≤ B (Hm p) := fun p => by
    rw [hHmΘ]
    exact (hΘP _).2
  -- smoothness
  have hD' : ContMDiff (𝓡∂ 2) I ∞ D' := (ContMDiff.subtypeVal_comp_iff U' _).mp hD
  have hG : ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ClosedCell 2 × Icc (0 : ℝ) 1 => ((p.2 : ℝ), D' p.1)) :=
    (contMDiff_subtypeVal_Icc.comp contMDiff_snd).prodMk (hD'.comp contMDiff_fst)
  have hHm : ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) I ∞ Hm :=
    contMDiff_subtype_val.comp (hFl.comp hG)
  refine ⟨Hm, hHm, ?_, ?_, fun p => ⟨hPHm p, hBHm p⟩, ?_, ?_, r', hr', ?_, U', Fl, hFl, hFl0,
    hFlgrp, hDU, fun p => ⟨hDU p.1, rfl⟩, hFlP, hFlB⟩
  · -- injective
    intro p p' h
    have ht : p.2 = p'.2 := Subtype.ext (by rw [← hPHm p, ← hPHm p', h])
    have h' : Fl (p.2 : ℝ) (D' p.1) = Fl (p.2 : ℝ) (D' p'.1) := by
      apply Subtype.ext
      change Hm p = (Fl ((p.2 : ℝ)) (D' p'.1) : Y)
      rw [h, ht]
    have h'' := congrArg Subtype.val ((Fl (p.2 : ℝ)).injective h')
    exact Prod.ext (hDinj h'') ht
  · -- injective differential
    intro p
    have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
    have hHmd : MDifferentiableAt ((𝓡∂ 2).prod (𝓡∂ 1)) I Hm p := (hHm p).mdifferentiableAt hn
    rw [injective_iff_map_eq_zero]
    intro v hv
    -- (i) the axial component vanishes
    have hPd : MDifferentiableAt I 𝓘(ℝ, ℝ) P (Hm p) := (hP (Hm p)).mdifferentiableAt hn
    have hcomp : P ∘ Hm = (Subtype.val : Icc (0 : ℝ) 1 → ℝ) ∘ Prod.snd := funext hPHm
    have h1 : mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) (P ∘ Hm) p v = 0 := by
      rw [mfderiv_comp p hPd hHmd, ContinuousLinearMap.comp_apply, hv, map_zero]
    rw [hcomp] at h1
    have hvald : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Icc (0 : ℝ) 1 → ℝ) p.2 :=
      (contMDiff_subtypeVal_Icc p.2).mdifferentiableAt hn
    have hsndd : MDifferentiableAt ((𝓡∂ 2).prod (𝓡∂ 1)) (𝓡∂ 1)
        (Prod.snd : ClosedCell 2 × Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1) p := mdifferentiableAt_snd
    rw [mfderiv_comp p hvald hsndd, mfderiv_snd] at h1
    change mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Icc (0 : ℝ) 1 → ℝ) p.2 v.2 = 0 at h1
    have hv2 : v.2 = 0 := by
      set L := mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Icc (0 : ℝ) 1 → ℝ) p.2 with hL
      have hL1 : L 1 = 1 := mfderiv_subtypeVal_Icc_one p.2
      have hne : (1 : TangentSpace (𝓡∂ 1) p.2) ≠ 0 := by
        intro h
        rw [h, map_zero] at hL1
        exact absurd hL1 (by norm_num : (0 : ℝ) ≠ 1)
      have hrank : Module.finrank ℝ (TangentSpace (𝓡∂ 1) p.2) = 1 :=
        finrank_euclideanSpace_fin
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : TangentSpace (𝓡∂ 1) p.2) hne).mp
        hrank v.2
      rw [← hc, map_smul, hL1] at h1
      have hc0 : c = 0 := by
        rcases smul_eq_zero.mp h1 with h | h
        · exact h
        · exact absurd (show (1 : ℝ) = 0 from h) one_ne_zero
      rw [← hc, hc0, zero_smul]
      rfl
    -- (ii) the disk component vanishes
    let ι : ClosedCell 2 → ClosedCell 2 × Icc (0 : ℝ) 1 := fun w => (w, p.2)
    have hιD : HasMFDerivAt (𝓡∂ 2) ((𝓡∂ 2).prod (𝓡∂ 1)) ι p.1
        ((ContinuousLinearMap.id ℝ (TangentSpace (𝓡∂ 2) p.1)).prod 0) :=
      (hasMFDerivAt_id p.1).prodMk (hasMFDerivAt_const p.2 p.1)
    have hιd : MDifferentiableAt (𝓡∂ 2) ((𝓡∂ 2).prod (𝓡∂ 1)) ι p.1 := hιD.mdifferentiableAt
    have hι : mfderiv (𝓡∂ 2) ((𝓡∂ 2).prod (𝓡∂ 1)) ι p.1 v.1 = v := by
      rw [hιD.mfderiv]
      exact Prod.ext rfl hv2.symm
    have hD'd : MDifferentiableAt (𝓡∂ 2) I D' p.1 := (hD' p.1).mdifferentiableAt hn
    have hFld : MDifferentiableAt I I (Fl (p.2 : ℝ)) (D' p.1) :=
      ((Fl (p.2 : ℝ)).contMDiff (D' p.1)).mdifferentiableAt hn
    have hvalU : MDifferentiableAt I I (Subtype.val : U' → Y) (Fl (p.2 : ℝ) (D' p.1)) :=
      (contMDiff_subtype_val (Fl (p.2 : ℝ) (D' p.1))).mdifferentiableAt hn
    have hfac : Hm ∘ ι = (Subtype.val : U' → Y) ∘ (Fl (p.2 : ℝ)) ∘ D' := rfl
    have h3 : mfderiv (𝓡∂ 2) I (Hm ∘ ι) p.1 v.1 = 0 := by
      rw [mfderiv_comp p.1 hHmd hιd]
      change mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) I Hm p
        (mfderiv (𝓡∂ 2) ((𝓡∂ 2).prod (𝓡∂ 1)) ι p.1 v.1) = 0
      rw [hι, hv]
    have hD'D : mfderiv (𝓡∂ 2) I D' p.1 = mfderiv (𝓡∂ 2) I D p.1 :=
      (DifferentialGeometry.Topology.mfderiv_subtypeVal_comp U' D' p.1).symm
    have h5 : mfderiv (𝓡∂ 2) I (Hm ∘ ι) p.1 v.1 =
        mfderiv I I (Fl (p.2 : ℝ)) (D' p.1) (mfderiv (𝓡∂ 2) I D p.1 v.1) := by
      rw [hfac, mfderiv_comp p.1 hvalU (hFld.comp p.1 hD'd), mfderiv_comp p.1 hFld hD'd,
        DifferentialGeometry.mfderiv_subtype_val, hD'D]
      rfl
    rw [h5] at h3
    have hinjFl := (((Fl (p.2 : ℝ)).isLocalDiffeomorph (D' p.1)).mfderivToContinuousLinearEquiv
      hn).injective
    have h4 : mfderiv (𝓡∂ 2) I D p.1 v.1 = 0 := by
      apply hinjFl
      change mfderiv I I (Fl (p.2 : ℝ)) (D' p.1) (mfderiv (𝓡∂ 2) I D p.1 v.1) =
        mfderiv I I (Fl (p.2 : ℝ)) (D' p.1) 0
      rw [map_zero]
      exact h3
    have hv1 : v.1 = 0 := hDimm p.1 (h4.trans (map_zero _).symm)
    exact Prod.ext hv1 hv2
  · -- range
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨by rw [hPHm]; exact p.2.2, hBHm p⟩
    · rintro ⟨hy01, hyB⟩
      have hyI : P y ∈ Ioo a₀ b₀ := ⟨by linarith [hy01.1], by linarith [hy01.2]⟩
      obtain ⟨hR, hΘy⟩ := hRΘ y hyI hyB
      obtain ⟨w, hw⟩ : R y ∈ range D := by rw [hDr]; exact hR
      refine ⟨(w, ⟨P y, hy01⟩), ?_⟩
      rw [hHmΘ]
      refine Eq.trans ?_ hΘy
      congr 1
      exact Prod.ext (Subtype.ext hw) rfl
  · -- the first end
    intro w
    change (Fl ((iccEnd false : Icc (0 : ℝ) 1) : ℝ) (D' w) : Y) = D w
    have h0' : ((iccEnd false : Icc (0 : ℝ) 1) : ℝ) = 0 := by simp [iccEnd]
    rw [h0', hFl0]
    rfl
  · -- polar on every slice
    intro p hp
    exact hFlB (D' p.1) p.2 (abs_lt.mpr ⟨by linarith [(hF0 p.1).2], hp⟩)

end GC.GraphManifold.Assembly.FC39P0
