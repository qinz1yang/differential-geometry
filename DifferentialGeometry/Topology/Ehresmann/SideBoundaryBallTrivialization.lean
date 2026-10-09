import DifferentialGeometry.Topology.Ehresmann.SideBoundaryBallTransport
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.PacketFibreSmooth

/-!
Parameterized radial transport gives a genuine smooth product over a finite dimensional ball
while preserving the actual side boundary. Normalizing at the zero parameter fixes the
original zero fibre without imposing a choice of horizontal lift on that fibre.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Manifold.RegularLevel

namespace DifferentialGeometry.Topology.Ehresmann

variable {E G H Y : Type*}
  [normE : NormedAddCommGroup E] [spaceE : NormedSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [normG : NormedAddCommGroup G] [spaceG : NormedSpace ℝ G]
  [finiteG : FiniteDimensional ℝ G]
  [topH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [boundaryI : I.Boundaryless]
  [topY : TopologicalSpace Y] [chartsY : ChartedSpace H Y]
  [smoothY : IsManifold I ∞ Y] [hausdorffY : T2Space Y]
  [sigmaY : SigmaCompactSpace Y]

omit finiteE finiteG boundaryI smoothY hausdorffY sigmaY in
private theorem parameter_base_rank {F : Type*}
    [normF : NormedAddCommGroup F] [spaceF : NormedSpace ℝ F] {P : Y → F}
    (hP : ContMDiff I 𝓘(ℝ, F) ∞ P) (w : G) (x : Y)
    (hr : Surjective (mfderiv I 𝓘(ℝ, F) P x)) :
    Surjective (mfderiv ((𝓘(ℝ, G)).prod I) 𝓘(ℝ, G × F)
      (fun p : G × Y => (p.1, P p.2)) (w, x)) := by
  change Surjective (mfderiv ((𝓘(ℝ, G)).prod I) 𝓘(ℝ, G × F)
    (Prod.map id P) (w, x))
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod, mfderiv_prodMap
    (mdifferentiableAt_id : MDiffAt (id : G → G) w)
    ((hP x).mdifferentiableAt (by simp)), mfderiv_id]
  intro q
  obtain ⟨v, hv⟩ := hr q.2
  refine ⟨(q.1, v), ?_⟩
  change (q.1, mfderiv I 𝓘(ℝ, F) P x v) = q
  rw [hv]
  exact Prod.eta q

omit finiteE finiteG boundaryI smoothY hausdorffY sigmaY in
private theorem parameter_boundary_rank {P : Y → G} {B : Y → ℝ}
    (hP : ContMDiff I 𝓘(ℝ, G) ∞ P) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    (w : G) (x : Y)
    (hr : Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (P y, B y)) x)) :
    Surjective (mfderiv ((𝓘(ℝ, G)).prod I) 𝓘(ℝ, (G × G) × ℝ)
      (fun p : G × Y => ((p.1, P p.2), B p.2)) (w, x)) := by
  let A := (ContinuousLinearEquiv.prodAssoc ℝ G G ℝ).symm.toDiffeomorph
  have hq := (hP.prodMk_space hB)
  have hf : ContMDiff ((𝓘(ℝ, G)).prod I) 𝓘(ℝ, G × (G × ℝ)) ∞
      (Prod.map id (fun y => (P y, B y))) :=
    (contMDiff_fst.prodMk_space (hq.comp contMDiff_snd))
  change Surjective (mfderiv ((𝓘(ℝ, G)).prod I) 𝓘(ℝ, (G × G) × ℝ)
    (A ∘ Prod.map id (fun y => (P y, B y))) (w, x))
  rw [mfderiv_comp (w, x) (A.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    ((hf (w, x)).mdifferentiableAt (by simp))]
  have hA := (A.mfderivToContinuousLinearEquiv (by simp) (w, (P x, B x))).surjective
  change Surjective (mfderiv 𝓘(ℝ, G × (G × ℝ)) 𝓘(ℝ, (G × G) × ℝ)
    A (w, (P x, B x))) at hA
  exact hA.comp (parameter_base_rank hq w x hr)

private theorem parameter_radial_transport {P : Y → G} {B : Y → ℝ}
    (hP : ContMDiff I 𝓘(ℝ, G) ∞ P) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    (b : ContDiffBump (0 : G))
    (hc : IsCompact (P ⁻¹' Metric.closedBall 0 b.rOut ∩ {x | 0 ≤ B x}))
    (hreg : ∀ x, P x ∈ Metric.closedBall 0 b.rOut → 0 ≤ B x →
      Surjective (mfderiv I 𝓘(ℝ, G) P x))
    (hregb : ∀ x, P x ∈ Metric.closedBall 0 b.rOut → B x = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (P y, B y)) x)) :
    ∃ U : TopologicalSpace.Opens (G × Y),
      (∀ w x, w ∈ Metric.closedBall 0 b.rOut → P x ∈ Metric.closedBall 0 b.rOut →
        0 ≤ B x → (w, x) ∈ U) ∧
      ∃ D : ℝ → U ≃ₘ⟮(𝓘(ℝ, G)).prod I, (𝓘(ℝ, G)).prod I⟯ U,
        ContMDiff (𝓘(ℝ, ℝ).prod ((𝓘(ℝ, G)).prod I)) ((𝓘(ℝ, G)).prod I) ∞
          (fun p : ℝ × U => D p.1 p.2) ∧
        (∀ s t x, D t (D s x) = D (s + t) x) ∧
        (∀ x, D 0 x = x) ∧
        ∀ (t : ℝ) (w : G) (x : Y) (hx : (w, x) ∈ U),
          w ∈ Metric.closedBall 0 b.rIn → P x ∈ Metric.closedBall 0 b.rIn →
          0 ≤ B x → P x + t • w ∈ Metric.closedBall 0 b.rIn →
          (D t ⟨(w, x), hx⟩).val.1 = w ∧
            P (D t ⟨(w, x), hx⟩).val.2 = P x + t • w ∧
            0 ≤ B (D t ⟨(w, x), hx⟩).val.2 := by
  let K := Metric.closedBall (0 : G) b.rOut
  let Q : G × Y → G × G := fun p => (p.1, P p.2)
  let C : G × Y → ℝ := fun p => B p.2
  have hQ : ContMDiff ((𝓘(ℝ, G)).prod I) 𝓘(ℝ, G × G) ∞ Q :=
    contMDiff_fst.prodMk_space (hP.comp contMDiff_snd)
  have hC : ContMDiff ((𝓘(ℝ, G)).prod I) 𝓘(ℝ, ℝ) ∞ C := hB.comp contMDiff_snd
  have hcompact : IsCompact (Q ⁻¹' (K ×ˢ K) ∩ {p | 0 ≤ C p}) := by
    have he : Q ⁻¹' (K ×ˢ K) ∩ {p | 0 ≤ C p} =
        K ×ˢ (P ⁻¹' K ∩ {x | 0 ≤ B x}) := by
      ext p
      exact and_assoc
    rw [he]
    exact (isCompact_closedBall (0 : G) b.rOut).prod hc
  obtain ⟨U, ho, hcontains, r, hr, hbuffer, hsQ, hsQB⟩ :=
    exists_sideBoundary_compactBase_margin hQ hC
      (Metric.isClosed_closedBall.prod Metric.isClosed_closedBall) hcompact
      (fun p hp hb => parameter_base_rank hP p.1 p.2 (hreg p.2 hp.2 hb))
      (fun p hp hb => parameter_boundary_rank hP hB p.1 p.2 (hregb p.2 hp.2 hb))
  let U₀ : TopologicalSpace.Opens (G × Y) := ⟨U, ho⟩
  let sigmaU : SigmaCompactSpace U₀ := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ((𝓘(ℝ, G)).prod I) ho)
  have hQr : ContMDiff ((𝓘(ℝ, G)).prod I) 𝓘(ℝ, G × G) ∞
      (fun x : U₀ => Q x) := hQ.comp contMDiff_subtype_val
  have hCr : ContMDiff ((𝓘(ℝ, G)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun x : U₀ => C x) := hC.comp contMDiff_subtype_val
  have hsupport : tsupport (sideBoundaryRadialField b) ⊆ K ×ˢ K := by
    simpa only [b.tsupport_eq] using sideBoundaryRadialField_support b
  have hbufferU : IsCompact {x : U₀ | Q x ∈ tsupport (sideBoundaryRadialField b) ∧
      -r ≤ C x} := by
    have hbig : IsCompact {x : U₀ | Q x ∈ K ×ˢ K ∧ -r ≤ C x} := by
      rw [Subtype.isCompact_iff]
      convert hbuffer using 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨hx, hq, hb⟩
        exact ⟨⟨x, hx⟩, ⟨hq, hb⟩, rfl⟩
    apply hbig.of_isClosed_subset
    · exact ((isClosed_tsupport (sideBoundaryRadialField b)).preimage hQr.continuous).inter
        (isClosed_le continuous_const hCr.continuous)
    · exact fun x hx => ⟨hsupport hx.1, hx.2⟩
  obtain ⟨X, hX, hDs, hrel, hinv⟩ := exists_sideBoundary_profileFlow hQr hCr
    (sideBoundaryRadialField b) (sideBoundaryRadialField_contDiff b)
    (sideBoundaryRadialField_compact b) r hr hbufferU
    (fun x hp hb => surjective_mfderiv_comp_opens_val U₀ x
      ((hQ x).mdifferentiableAt (by simp)) (hsQ x x.2))
    (fun x hp hb => surjective_mfderiv_comp_opens_val U₀ x
      (((hQ.prodMk_space hC) x).mdifferentiableAt (by simp)) (hsQB x x.2 hb))
  let D := compactSupportFlowDiffeomorph X X.contMDiff hX
  refine ⟨U₀, fun w x hw hx hb => hcontains ⟨⟨hw, hx⟩, hb⟩, D, hDs, ?_, ?_, ?_⟩
  · intro s t x
    exact congrArg (fun F : U₀ ≃ₘ⟮(𝓘(ℝ, G)).prod I, (𝓘(ℝ, G)).prod I⟯ U₀ => F x)
      (compactSupportFlowDiffeomorph_trans X X.contMDiff hX s t)
  · intro x
    exact congrArg (fun F : U₀ ≃ₘ⟮(𝓘(ℝ, G)).prod I, (𝓘(ℝ, G)).prod I⟯ U₀ => F x)
      (compactSupportFlowDiffeomorph_zero X X.contMDiff hX)
  · intro t w x hx hw hp hb hpt
    have he := hrel t ⟨(w, x), hx⟩
    have hχ : sideProfile r (B x) ∈ Icc (0 : ℝ) (1 / 2) :=
      ⟨(sideProfile_nonneg_iff hr).mpr hb, sideProfile_le_half r (B x)⟩
    have hflow := sideBoundaryRadialField_flow b w (P x) (sideProfile r (B x)) t
      hw hp hχ hpt
    rw [hflow] at he
    refine ⟨congrArg (fun q => q.1.1) he, congrArg (fun q => q.1.2) he,
      (hinv t ⟨(w, x), hx⟩).2.mpr hb⟩

private def parameterFlowValue
    (U : TopologicalSpace.Opens (G × Y))
    (D : ℝ → U ≃ₘ⟮(𝓘(ℝ, G)).prod I, (𝓘(ℝ, G)).prod I⟯ U)
    (t : ℝ) (a : Y → G) (x : Y) : Y := by
  classical
  exact if hx : (a x, x) ∈ U then (D t ⟨(a x, x), hx⟩).val.2 else x

omit finiteE finiteG boundaryI smoothY hausdorffY sigmaY in
private theorem parameter_flow_value_smooth
    (U : TopologicalSpace.Opens (G × Y))
    (D : ℝ → U ≃ₘ⟮(𝓘(ℝ, G)).prod I, (𝓘(ℝ, G)).prod I⟯ U)
    (t : ℝ) (a : Y → G) (ha : ContMDiff I 𝓘(ℝ, G) ∞ a) :
    ContMDiffOn I I ∞ (parameterFlowValue U D t a) {x | (a x, x) ∈ U} := by
  classical
  intro x hx
  let nonemptyU : Nonempty U := ⟨⟨(a x, x), hx⟩⟩
  let φ := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    ((𝓘(ℝ, G)).prod I) U nonemptyU
  have hφ : ContMDiffAt ((𝓘(ℝ, G)).prod I) ((𝓘(ℝ, G)).prod I) ∞ φ.symm (a x, x) :=
    φ.symm.contMDiffOn.contMDiffAt (φ.open_target.mem_nhds (by
      rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
      exact hx))
  have hpair : ContMDiff I ((𝓘(ℝ, G)).prod I) ∞ (fun y => (a y, y)) :=
    ha.prodMk contMDiff_id
  have hlift : ContMDiffAt I ((𝓘(ℝ, G)).prod I) ∞
      (fun y => φ.symm (a y, y)) x := hφ.comp x (f := fun y : Y => (a y, y)) (hpair x)
  have hvalue : ContMDiffAt I I ∞ (fun y => (D t (φ.symm (a y, y))).val.2) x :=
    contMDiff_snd.contMDiffAt.comp x (contMDiff_subtype_val.contMDiffAt.comp x
      ((D t).contMDiff.contMDiffAt.comp x hlift))
  apply ContMDiffAt.contMDiffWithinAt
  apply hvalue.congr_of_eventuallyEq
  filter_upwards [(U.isOpen.preimage hpair.continuous).mem_nhds hx] with y hy
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply
    ((𝓘(ℝ, G)).prod I) U nonemptyU hy]
  change (a y, y) ∈ U at hy
  rw [parameterFlowValue, dite_eq_left hy]

theorem exists_sideBoundary_ball_trivialization {d : ℕ}
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ G)
  {P : Y → G} {B : Y → ℝ}
  (hP : ContMDiff I 𝓘(ℝ, G) ∞ P) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
  {R R₀ : ℝ} (hR : 0 < R) (hRR : R < R₀)
  (hreg : ∀ y, P y ∈ Metric.ball 0 R₀ → 0 ≤ B y →
    Surjective (mfderiv I 𝓘(ℝ, G) P y))
  (hregb : ∀ y, P y ∈ Metric.ball 0 R₀ → B y = 0 →
    Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun z => (P z, B z)) y))
  (hproper : ∀ K : Set G, IsCompact K → K ⊆ Metric.ball 0 R₀ →
    IsCompact (P ⁻¹' K ∩ {y | 0 ≤ B y})) :
  let sourceCharts := regularSublevelChartedSpace hdim hP hB
    (fun y hy hb => hreg y (by rw [hy]; exact Metric.mem_ball_self (hR.trans hRR)) hb)
    (fun y hy hb => hregb y (by rw [hy]; exact Metric.mem_ball_self (hR.trans hRR)) hb)
  let base : TopologicalSpace.Opens G := ⟨Metric.ball 0 R, Metric.isOpen_ball⟩
  ∃ Θ : {y : Y // P y = 0 ∧ 0 ≤ B y} × base → Y,
    ContMDiff ((𝓡∂ (d + 1)).prod 𝓘(ℝ, G)) I ∞ Θ ∧
    (∀ p, P (Θ p) = p.2 ∧ 0 ≤ B (Θ p)) ∧
    (∀ x, Θ (x, ⟨0, Metric.mem_ball_self hR⟩) = x) ∧
    Injective Θ ∧
    ∃ O : Set Y, IsOpen O ∧ (∀ y, P y ∈ base → 0 ≤ B y → y ∈ O) ∧
      ∃ Rmap : Y → Y, ContMDiffOn I I ∞ Rmap O ∧
        ∀ y (hy : P y ∈ base), 0 ≤ B y →
          ∃ hr : P (Rmap y) = 0 ∧ 0 ≤ B (Rmap y),
            Θ (⟨Rmap y, hr⟩, ⟨P y, hy⟩) = y := by
  classical
  let hreg0 := fun (y : Y) (hy : P y = 0) (hb : 0 ≤ B y) => hreg y
    (by rw [hy]; exact Metric.mem_ball_self (hR.trans hRR)) hb
  let hregb0 := fun (y : Y) (hy : P y = 0) (hb : B y = 0) => hregb y
    (by rw [hy]; exact Metric.mem_ball_self (hR.trans hRR)) hb
  let sourceCharts := regularSublevelChartedSpace hdim hP hB hreg0 hregb0
  let F := {y : Y // P y = 0 ∧ 0 ≤ B y}
  let base : TopologicalSpace.Opens G := ⟨Metric.ball 0 R, Metric.isOpen_ball⟩
  let b : ContDiffBump (0 : G) :=
    { rIn := (R + R₀) / 2, rOut := (R + 3 * R₀) / 4,
      rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  have hkin : Metric.closedBall (0 : G) b.rOut ⊆ Metric.ball 0 R₀ :=
    Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  have hinner : Metric.ball (0 : G) R ⊆ Metric.closedBall 0 b.rIn :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by
      dsimp [b]; linarith))
  have hzero : (0 : G) ∈ Metric.closedBall 0 b.rIn :=
    Metric.mem_closedBall_self b.rIn_pos.le
  have houter : Metric.closedBall (0 : G) b.rIn ⊆ Metric.closedBall 0 b.rOut :=
    Metric.closedBall_subset_closedBall b.rIn_lt_rOut.le
  obtain ⟨U, hU, D, -, hadd, hD0, htr⟩ := parameter_radial_transport hP hB b
    (hproper _ (isCompact_closedBall 0 b.rOut) hkin)
    (fun x hx hb => hreg x (hkin hx) hb)
    (fun x hx hb => hregb x (hkin hx) hb)
  have hfx : ∀ x : F, P x = 0 := fun x => x.2.1
  have hfmem : ∀ x : F, (0, x.val) ∈ U := fun x => hU 0 x
    (houter hzero) (by rw [hfx]; exact houter hzero) x.2.2
  let i0 : F → U := fun x => ⟨(0, x.val), hfmem x⟩
  have hi0 : ContMDiff (𝓡∂ (d + 1)) ((𝓘(ℝ, G)).prod I) ∞ i0 := by
    apply (ContMDiff.subtypeVal_comp_iff U i0).mp
    exact contMDiff_const.prodMk (regularSublevel_contMDiff_val hdim hP hB hreg0 hregb0)
  let n0 : F → Y := fun x => (D (-1) (i0 x)).val.2
  have hn0 : ContMDiff (𝓡∂ (d + 1)) I ∞ n0 :=
    contMDiff_snd.comp (contMDiff_subtype_val.comp ((D (-1)).contMDiff.comp hi0))
  have hn0data : ∀ x : F, (D (-1) (i0 x)).val.1 = 0 ∧ P (n0 x) = 0 ∧ 0 ≤ B (n0 x) := by
    intro x
    have hp : P x ∈ Metric.closedBall 0 b.rIn := by rw [hfx]; exact hzero
    have he := htr (-1) 0 x.val (hfmem x) hzero hp x.2.2 (by
      simpa only [smul_zero, add_zero] using hp)
    simpa only [smul_zero, add_zero, hfx] using he
  have hnormalized : ∀ x : F, (0, n0 x) = (D (-1) (i0 x)).val := by
    intro x
    exact Prod.ext (hn0data x).1.symm rfl
  let incl : F × base → U := fun p => ⟨(p.2.val, n0 p.1),
    hU p.2 (n0 p.1) (houter (hinner p.2.2))
      (by rw [(hn0data p.1).2.1]; exact houter hzero) (hn0data p.1).2.2⟩
  have hincl : ContMDiff ((𝓡∂ (d + 1)).prod 𝓘(ℝ, G)) ((𝓘(ℝ, G)).prod I) ∞ incl := by
    apply (ContMDiff.subtypeVal_comp_iff U incl).mp
    exact (contMDiff_subtype_val.comp contMDiff_snd).prodMk (hn0.comp contMDiff_fst)
  let Θ : F × base → Y := fun p => (D 1 (incl p)).val.2
  have hΘs : ContMDiff ((𝓡∂ (d + 1)).prod 𝓘(ℝ, G)) I ∞ Θ :=
    contMDiff_snd.comp (contMDiff_subtype_val.comp ((D 1).contMDiff.comp hincl))
  have hΘdata : ∀ p : F × base, P (Θ p) = p.2 ∧ 0 ≤ B (Θ p) := by
    intro p
    have hp : P (n0 p.1) ∈ Metric.closedBall 0 b.rIn := by
      rw [(hn0data p.1).2.1]
      exact hzero
    have he := htr 1 p.2 (n0 p.1) (incl p).2 (hinner p.2.2) hp
      (hn0data p.1).2.2 (by
        rw [(hn0data p.1).2.1, one_smul, zero_add]
        exact hinner p.2.2)
    refine ⟨?_, he.2.2⟩
    simpa only [(hn0data p.1).2.1, one_smul, zero_add] using he.2.1
  refine ⟨Θ, hΘs, hΘdata, ?_, ?_, ?_⟩
  · intro x
    have hi : incl (x, ⟨0, Metric.mem_ball_self hR⟩) = D (-1) (i0 x) :=
      Subtype.ext (hnormalized x)
    change (D 1 (incl (x, ⟨0, Metric.mem_ball_self hR⟩))).val.2 = x.val
    rw [hi, hadd, neg_add_cancel, hD0]
  · intro p q hpq
    have hw : p.2 = q.2 := Subtype.ext
      ((hΘdata p).1.symm.trans ((congrArg P hpq).trans (hΘdata q).1))
    have hfirst : (D 1 (incl p)).val.1 = p.2.val := by
      have he := htr 1 p.2 (n0 p.1) (incl p).2 (hinner p.2.2)
        (by rw [(hn0data p.1).2.1]; exact hzero) (hn0data p.1).2.2 (by
          rw [(hn0data p.1).2.1, one_smul, zero_add]
          exact hinner p.2.2)
      exact he.1
    have hsecond : (D 1 (incl q)).val.1 = q.2.val := by
      have he := htr 1 q.2 (n0 q.1) (incl q).2 (hinner q.2.2)
        (by rw [(hn0data q.1).2.1]; exact hzero) (hn0data q.1).2.2 (by
          rw [(hn0data q.1).2.1, one_smul, zero_add]
          exact hinner q.2.2)
      exact he.1
    have hi : incl p = incl q := (D 1).injective (Subtype.ext (Prod.ext
      (hfirst.trans ((congrArg Subtype.val hw).trans hsecond.symm)) hpq))
    have hn := congrArg (fun x : U => x.val.2) hi
    change n0 p.1 = n0 q.1 at hn
    have hminus : D (-1) (i0 p.1) = D (-1) (i0 q.1) :=
      Subtype.ext ((hnormalized p.1).symm.trans
        ((congrArg (fun x : Y => ((0 : G), x)) hn).trans (hnormalized q.1)))
    have hx := congrArg (fun x : U => x.val.2) ((D (-1)).injective hminus)
    exact Prod.ext (Subtype.ext hx) hw
  · let V0 : Set Y := {x | ((0 : G), x) ∈ U}
    let V1 : Set Y := {x | (P x, x) ∈ U}
    let A : Y → Y := parameterFlowValue U D (-1) P
    let Z : Y → Y := parameterFlowValue U D 1 (fun x => (0 : G))
    have hV0 : IsOpen V0 := U.isOpen.preimage (continuous_const.prodMk continuous_id)
    have hV1 : IsOpen V1 := U.isOpen.preimage (hP.continuous.prodMk continuous_id)
    have hA : ContMDiffOn I I ∞ A V1 := parameter_flow_value_smooth U D (-1) P hP
    have hZ : ContMDiffOn I I ∞ Z V0 :=
      parameter_flow_value_smooth U D 1 (fun x => (0 : G)) contMDiff_const
    let O := V1 ∩ A ⁻¹' V0
    have hO : IsOpen O := hA.continuousOn.isOpen_inter_preimage hV1 hV0
    have hAy : ∀ y, P y ∈ base → 0 ≤ B y →
        y ∈ V1 ∧ P (A y) = 0 ∧ 0 ≤ B (A y) ∧ (0, A y) ∈ U := by
      intro y hy hb
      have hw := hinner hy
      have hyU : (P y, y) ∈ U := hU (P y) y (houter hw) (houter hw) hb
      have he := htr (-1) (P y) y hyU hw hw hb (by
        simpa only [neg_one_smul, add_neg_cancel] using hzero)
      have hval : A y = (D (-1) ⟨(P y, y), hyU⟩).val.2 := by
        simp only [A, parameterFlowValue, dite_eq_left hyU]
      have hpa : P (A y) = 0 := by
        rw [hval]
        simpa only [neg_one_smul, add_neg_cancel] using he.2.1
      have hba : 0 ≤ B (A y) := by rw [hval]; exact he.2.2
      exact ⟨hyU, hpa, hba, hU 0 (A y) (houter hzero)
        (by rw [hpa]; exact houter hzero) hba⟩
    refine ⟨O, hO, fun y hy hb => ⟨(hAy y hy hb).1, (hAy y hy hb).2.2.2⟩,
      Z ∘ A, hZ.comp' hA, ?_⟩
    intro y hy hb
    have hyU := (hAy y hy hb).1
    change (P y, y) ∈ U at hyU
    have haU := (hAy y hy hb).2.2.2
    have haP := (hAy y hy hb).2.1
    have haB := (hAy y hy hb).2.2.1
    have haz : A y = (D (-1) ⟨(P y, y), hyU⟩).val.2 := by
      simp only [A, parameterFlowValue, dite_eq_left hyU]
    have hzy : (Z ∘ A) y = (D 1 ⟨(0, A y), haU⟩).val.2 := by
      simp only [Function.comp_apply, Z, parameterFlowValue, dite_eq_left haU]
    have he := htr 1 0 (A y) haU hzero (by rw [haP]; exact hzero) haB (by
      rw [haP, smul_zero, zero_add]
      exact hzero)
    have hrp : P ((Z ∘ A) y) = 0 := by
      rw [hzy]
      simpa only [haP, smul_zero, zero_add] using he.2.1
    have hrb : 0 ≤ B ((Z ∘ A) y) := by rw [hzy]; exact he.2.2
    refine ⟨⟨hrp, hrb⟩, ?_⟩
    let z : U := ⟨(0, A y), haU⟩
    have hiz : i0 ⟨(Z ∘ A) y, ⟨hrp, hrb⟩⟩ = D 1 z := by
      apply Subtype.ext
      exact Prod.ext he.1.symm hzy
    have hnormal : D (-1) (i0 ⟨(Z ∘ A) y, ⟨hrp, hrb⟩⟩) = z := by
      rw [hiz, hadd, add_neg_cancel, hD0]
    have hnval : n0 ⟨(Z ∘ A) y, ⟨hrp, hrb⟩⟩ = A y :=
      congrArg (fun x : U => x.val.2) hnormal
    have hi : incl (⟨(Z ∘ A) y, ⟨hrp, hrb⟩⟩, ⟨P y, hy⟩) =
        D (-1) ⟨(P y, y), hyU⟩ := by
      apply Subtype.ext
      have hf := (htr (-1) (P y) y hyU (hinner hy) (hinner hy) hb (by
        simpa only [neg_one_smul, add_neg_cancel] using hzero)).1
      exact Prod.ext hf.symm (hnval.trans haz)
    change (D 1 (incl (⟨(Z ∘ A) y, ⟨hrp, hrb⟩⟩, ⟨P y, hy⟩))).val.2 = y
    rw [hi, hadd, neg_add_cancel, hD0]


end DifferentialGeometry.Topology.Ehresmann
