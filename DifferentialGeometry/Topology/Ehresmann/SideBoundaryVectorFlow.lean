import DifferentialGeometry.Topology.Ehresmann.SideBoundaryInterval
import DifferentialGeometry.Topology.Ehresmann.BallTrivialization

/-!
A compact base vector field admits an actual compact smooth lift preserving the side profile.
The base may have any finite dimension; the construction uses the rank of the base map in the
interior and the joint base and boundary rank near the side. This supplies complete flows for
radial ball transport without assuming a family of source diffeomorphisms.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Analysis.ODE

variable {E G H M : Type*}
  [normE : NormedAddCommGroup E] [spaceE : NormedSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [normG : NormedAddCommGroup G] [spaceG : NormedSpace ℝ G]
  [finiteG : FiniteDimensional ℝ G]
  [topH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [boundaryI : I.Boundaryless]
  [topM : TopologicalSpace M] [chartsM : ChartedSpace H M]
  [smoothM : IsManifold I ∞ M] [hausdorffM : T2Space M]
  [sigmaM : SigmaCompactSpace M]

def sideBoundaryProfileBump : ContDiffBump (1 / 4 : ℝ) :=
  ⟨3 / 8, 1 / 2, by norm_num, by norm_num⟩

def sideBoundaryProfileField (V : G → G) (y : G × ℝ) : G × ℝ :=
  (sideBoundaryProfileBump y.2 • V y.1, 0)

omit finiteE finiteG topH boundaryI topM chartsM smoothM hausdorffM sigmaM in
theorem sideBoundaryProfileField_contDiff {V : G → G} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (sideBoundaryProfileField V) :=
  ((sideBoundaryProfileBump.contDiff.comp contDiff_snd).smul
    (hV.comp contDiff_fst)).prodMk contDiff_const

omit finiteE finiteG topH boundaryI topM chartsM smoothM hausdorffM sigmaM in
theorem sideBoundaryProfileField_support (V : G → G) :
    tsupport (sideBoundaryProfileField V) ⊆
      tsupport V ×ˢ tsupport sideBoundaryProfileBump := by
  apply closure_minimal
  · intro y hy
    constructor
    · apply subset_tsupport
      intro hv
      apply hy
      simp only [sideBoundaryProfileField, hv, smul_zero, Prod.zero_eq_mk]
    · apply subset_tsupport
      intro hb
      apply hy
      simp only [sideBoundaryProfileField, hb, zero_smul, Prod.zero_eq_mk]
  · exact (isClosed_tsupport V).prod (isClosed_tsupport sideBoundaryProfileBump)

omit finiteE finiteG topH boundaryI topM chartsM smoothM hausdorffM sigmaM in
theorem sideBoundaryProfileField_compact {V : G → G} (hV : HasCompactSupport V) :
    HasCompactSupport (sideBoundaryProfileField V) :=
  (hV.isCompact.prod sideBoundaryProfileBump.hasCompactSupport.isCompact).of_isClosed_subset
    (isClosed_tsupport (sideBoundaryProfileField V)) (sideBoundaryProfileField_support V)

omit finiteE normG spaceG finiteG topH boundaryI topM chartsM smoothM hausdorffM sigmaM in
theorem sideBoundaryProfileBump_lower {u : ℝ} (hu : u ∈ tsupport sideBoundaryProfileBump) :
    -(1 / 4 : ℝ) ≤ u := by
  rw [sideBoundaryProfileBump.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, abs_le] at hu
  change -(1 / 2 : ℝ) ≤ u - 1 / 4 ∧ u - 1 / 4 ≤ 1 / 2 at hu
  linarith [hu.1]

omit finiteE normG spaceG finiteG topH boundaryI topM chartsM smoothM hausdorffM sigmaM in
theorem sideBoundaryProfileBump_one {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (1 / 2)) :
    sideBoundaryProfileBump u = 1 := by
  apply sideBoundaryProfileBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  change -(3 / 8 : ℝ) ≤ u - 1 / 4 ∧ u - 1 / 4 ≤ 3 / 8
  constructor <;> linarith [hu.1, hu.2]

omit finiteE finiteG boundaryI smoothM hausdorffM sigmaM in
private theorem vector_pair_derivative {P : M → G} {B : M → ℝ}
    (hP : ContMDiff I 𝓘(ℝ, G) ∞ P) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    (x : M) (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (P y, B y)) x v =
      (mfderiv I 𝓘(ℝ, G) P x v, mvfderiv I B x v) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
    mfderiv_prodMk ((hP x).mdifferentiableAt (by simp))
      ((hB x).mdifferentiableAt (by simp))]
  rfl

omit finiteE finiteG boundaryI smoothM hausdorffM sigmaM in
private theorem sideProfile_derivative_pair {P : M → G} {B : M → ℝ}
    (hP : ContMDiff I 𝓘(ℝ, G) ∞ P) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    (r : ℝ) (x : M) (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (P y, sideProfile r (B y))) x v =
      (mfderiv I 𝓘(ℝ, G) P x v, deriv (sideProfile r) (B x) * mvfderiv I B x v) := by
  have hc := (contDiff_sideProfile r).contMDiff.comp hB
  change mfderiv I 𝓘(ℝ, G × ℝ)
    (fun y => (P y, (sideProfile r ∘ B) y)) x v = _
  rw [vector_pair_derivative hP hc]
  congr 1
  exact mvfderiv_comp_real ((hB x).mdifferentiableAt (by simp))
    (((contDiff_sideProfile r).differentiable (by simp)) (B x)) v

omit boundaryI in
theorem exists_sideBoundary_profileLift {P : M → G} {B : M → ℝ}
    (hP : ContMDiff I 𝓘(ℝ, G) ∞ P) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    (V : G → G) (hV : ContDiff ℝ ∞ V)
    (r : ℝ) (hr : 0 < r)
    (hC : IsCompact {x | P x ∈ tsupport V ∧ -r ≤ B x})
    (hsP : ∀ x, P x ∈ tsupport V → -r ≤ B x →
      Surjective (mfderiv I 𝓘(ℝ, G) P x))
    (hsPB : ∀ x, P x ∈ tsupport V → |B x| < r →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (P y, B y)) x)) :
    ∃ X : Cₛ^∞⟮I; E, TangentSpace I⟯,
      IsCompact (tsupport X) ∧
      ∀ x, mfderiv I 𝓘(ℝ, G × ℝ)
        (fun y => (P y, sideProfile r (B y))) x (X x) =
          sideBoundaryProfileField V (P x, sideProfile r (B x)) := by
  let Q : M → G × ℝ := fun x => (P x, sideProfile r (B x))
  have hQ := hP.prodMk_space ((contDiff_sideProfile r).contMDiff.comp hB)
  have hlocal : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ L : (y : M) → TangentSpace I y,
      ContMDiffOn I I.tangent ∞
        (fun y => (⟨y, L y⟩ : TangentBundle I M)) U ∧
      (∀ y ∈ U, mfderiv I 𝓘(ℝ, G × ℝ) Q y (L y) = sideBoundaryProfileField V (Q y)) ∧
      (∀ y ∈ U, sideBoundaryProfileField V (Q y) = 0 → L y = 0) := by
    intro x
    by_cases ha : Q x ∈ tsupport (sideBoundaryProfileField V)
    · obtain ⟨hp, hc⟩ := sideBoundaryProfileField_support V ha
      have hb : -(r / 2) < B x :=
        neg_half_lt_of_sideProfile_ge hr (sideBoundaryProfileBump_lower hc)
      by_cases hnear : |B x| < r
      · let W : G × ℝ → G × ℝ := fun p =>
          sideBoundaryProfileField V (p.1, sideProfile r p.2)
        have hw : ContDiff ℝ ∞ W := (sideBoundaryProfileField_contDiff hV).comp
          (contDiff_fst.prodMk ((contDiff_sideProfile r).comp contDiff_snd))
        obtain ⟨U, hu, L, hl, he, hz⟩ := exists_local_smoothDerivativeLift_of_surjective
          (fun y => (P y, B y)) (hP.prodMk_space hB) W
          (contMDiff_vectorSpace_iff_contDiff.mpr hw) x (hsPB x hp hnear)
        refine ⟨U, hu, L, hl, ?_, hz⟩
        intro y hy
        have hrel := he y hy
        rw [vector_pair_derivative hP hB] at hrel
        have h1 := congrArg Prod.fst hrel
        have h2 := congrArg Prod.snd hrel
        change mvfderiv I B y (L y) = 0 at h2
        rw [sideProfile_derivative_pair hP hB]
        change (_, _) = (_, _)
        apply Prod.ext
        · exact h1
        · change deriv (sideProfile r) (B y) * mvfderiv I B y (L y) = 0
          rw [h2, mul_zero]
      · have hbfar : r / 2 < B x := by
          have hab := le_abs'.mp (not_lt.mp hnear)
          rcases hab with hab | hab <;> linarith
        let W : G → G := fun p => sideBoundaryProfileBump (1 / 2) • V p
        have hw : ContDiff ℝ ∞ W := contDiff_const.smul hV
        obtain ⟨U, hu, L, hl, he, hz⟩ := exists_local_smoothDerivativeLift_of_surjective
          P hP W (contMDiff_vectorSpace_iff_contDiff.mpr hw) x (hsP x hp (by linarith))
        have ho : IsOpen {y | r / 2 < B y} := isOpen_lt continuous_const hB.continuous
        refine ⟨U ∩ {y | r / 2 < B y}, inter_mem hu (ho.mem_nhds hbfar), L,
          hl.mono inter_subset_left, ?_, ?_⟩
        · intro y hy
          have hprof := sideProfile_of_ge hr hy.2.le
          have hder := deriv_sideProfile_eq_zero hr
            (hy.2.trans_le (le_abs_self (B y)))
          rw [sideProfile_derivative_pair hP hB, he y hy.1, hder, zero_mul]
          simp only [Q, sideBoundaryProfileField, hprof, W]
          rfl
        · intro y hy hzq
          apply hz y hy.1
          have heq := congrArg Prod.fst hzq
          change sideBoundaryProfileBump (sideProfile r (B y)) • V (P y) = 0 at heq
          rw [sideProfile_of_ge hr hy.2.le] at heq
          exact heq
    · have ho := (isClosed_tsupport (sideBoundaryProfileField V)).isOpen_compl.preimage
        hQ.continuous
      refine ⟨Q ⁻¹' (tsupport (sideBoundaryProfileField V))ᶜ, ho.mem_nhds ha,
        fun y => 0, (Bundle.contMDiff_zeroSection ℝ (TangentSpace I)).contMDiffOn, ?_, ?_⟩
      · intro y hy
        rw [map_zero]
        exact (image_eq_zero_of_notMem_tsupport hy).symm
      · intro y hy hz
        rfl
  obtain ⟨X, hx, hsupport⟩ := exists_smoothDerivativeLift_of_local Q hQ.continuous
    (sideBoundaryProfileField V) hlocal
  refine ⟨X, hC.of_isClosed_subset (isClosed_tsupport X) ?_, hx⟩
  intro x hxt
  obtain ⟨hp, hb⟩ := sideBoundaryProfileField_support V (hsupport hxt)
  have hbound := neg_half_lt_of_sideProfile_ge hr (sideBoundaryProfileBump_lower hb)
  exact ⟨hp, by linarith⟩

omit finiteE topH boundaryI topM chartsM smoothM hausdorffM sigmaM in
private theorem sideBoundaryProfileField_flow_snd {V : G → G}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (t : ℝ) (y : G × ℝ) :
    (compactSupportFlowDiffeomorph (sideBoundaryProfileField V)
      (contMDiff_vectorSpace_iff_contDiff.mpr (sideBoundaryProfileField_contDiff hV))
      (sideBoundaryProfileField_compact hVc) t y).2 = y.2 := by
  let completeG : CompleteSpace G := FiniteDimensional.complete ℝ G
  have hd : ∀ z : G × ℝ,
      mfderiv 𝓘(ℝ, G × ℝ) 𝓘(ℝ, ℝ) Prod.snd z (sideBoundaryProfileField V z) = 0 := by
    intro z
    rw [mfderiv_eq_fderiv, fderiv_snd]
    rfl
  have hc : IsCompact (tsupport (fun z : ℝ => (0 : ℝ))) := by
    have he : tsupport (fun z : ℝ => (0 : ℝ)) = ∅ := tsupport_eq_empty_iff.mpr rfl
    rw [he]
    exact isCompact_empty
  have hm := compactSupportFlowDiffeomorph_map_of_mfderiv_eq Prod.snd
    ((contDiff_snd : ContDiff ℝ 1 (Prod.snd : G × ℝ → ℝ)).contMDiff)
    (sideBoundaryProfileField V)
    (contMDiff_vectorSpace_iff_contDiff.mpr (sideBoundaryProfileField_contDiff hV))
    (sideBoundaryProfileField_compact hVc) (fun z : ℝ => (0 : TangentSpace 𝓘(ℝ, ℝ) z))
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, ℝ))) hc hd t y
  rw [hm, compactSupportFlowDiffeomorph_zeroField]
  rfl

theorem exists_sideBoundary_profileFlow {P : M → G} {B : M → ℝ}
    (hP : ContMDiff I 𝓘(ℝ, G) ∞ P) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    (V : G → G) (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (r : ℝ) (hr : 0 < r)
    (hC : IsCompact {x | P x ∈ tsupport V ∧ -r ≤ B x})
    (hsP : ∀ x, P x ∈ tsupport V → -r ≤ B x →
      Surjective (mfderiv I 𝓘(ℝ, G) P x))
    (hsPB : ∀ x, P x ∈ tsupport V → |B x| < r →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (P y, B y)) x)) :
    ∃ (X : Cₛ^∞⟮I; E, TangentSpace I⟯) (hc : IsCompact (tsupport X)),
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
        (fun p : ℝ × M => compactSupportFlowDiffeomorph X X.contMDiff hc p.1 p.2) ∧
      (∀ t x, (P (compactSupportFlowDiffeomorph X X.contMDiff hc t x),
        sideProfile r (B (compactSupportFlowDiffeomorph X X.contMDiff hc t x))) =
          compactSupportFlowDiffeomorph (sideBoundaryProfileField V)
            (contMDiff_vectorSpace_iff_contDiff.mpr (sideBoundaryProfileField_contDiff hV))
            (sideBoundaryProfileField_compact hVc) t (P x, sideProfile r (B x))) ∧
      ∀ t x,
        sideProfile r (B (compactSupportFlowDiffeomorph X X.contMDiff hc t x)) =
          sideProfile r (B x) ∧
        (0 ≤ B (compactSupportFlowDiffeomorph X X.contMDiff hc t x) ↔ 0 ≤ B x) := by
  let completeE : CompleteSpace E := FiniteDimensional.complete ℝ E
  let completeG : CompleteSpace G := FiniteDimensional.complete ℝ G
  obtain ⟨X, hc, hd⟩ := exists_sideBoundary_profileLift hP hB V hV r hr hC hsP hsPB
  have hQ := hP.prodMk_space ((contDiff_sideProfile r).contMDiff.comp hB)
  have hm := compactSupportFlowDiffeomorph_map_of_mfderiv_eq
    (fun x => (P x, sideProfile r (B x))) (hQ.of_le (by norm_num))
    X X.contMDiff hc (sideBoundaryProfileField V)
    (contMDiff_vectorSpace_iff_contDiff.mpr (sideBoundaryProfileField_contDiff hV))
    (sideBoundaryProfileField_compact hVc) hd
  refine ⟨X, hc, contMDiff_globalFlow_joint_of_compactSupport X X.contMDiff hc, hm, ?_⟩
  intro t x
  have he := congrArg Prod.snd (hm t x)
  rw [sideBoundaryProfileField_flow_snd hV hVc] at he
  refine ⟨he, ?_⟩
  rw [← sideProfile_nonneg_iff hr, ← sideProfile_nonneg_iff hr (u := B x)]
  change sideProfile r (B (compactSupportFlowDiffeomorph X X.contMDiff hc t x)) =
    sideProfile r (B x) at he
  rw [he]

end DifferentialGeometry.Topology.Ehresmann
