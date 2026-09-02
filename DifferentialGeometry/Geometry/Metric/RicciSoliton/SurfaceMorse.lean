import DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceIdentities
import DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceFlux
import DifferentialGeometry.Geometry.Operator.HessianExtrema
import DifferentialGeometry.Topology.Morse.CriticalPoints
import DifferentialGeometry.Topology.Morse.NoCriticalValues
import DifferentialGeometry.Topology.Morse.Riemannian

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Topology.Morse

variable {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [ConnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma strictMonoOn_mul_exp_neg_Iic_one :
    StrictMonoOn (fun x : Real => x * Real.exp (-x)) (Set.Iic 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic 1) (by fun_prop)
  intro x hx
  rw [interior_Iic] at hx
  change x < 1 at hx
  have hexp : HasDerivAt (fun y : Real => Real.exp (-y))
      (-Real.exp (-x)) x := by
    simpa using! (hasDerivAt_neg x).exp
  have hderiv : HasDerivAt (fun y : Real => y * Real.exp (-y))
      ((1 - x) * Real.exp (-x)) x := by
    simpa [sub_mul] using! (hasDerivAt_id x).mul hexp
  rw [hderiv.deriv]
  exact mul_pos (sub_pos.mpr hx) (Real.exp_pos _)

private lemma strictAntiOn_mul_exp_neg_Ici_one :
    StrictAntiOn (fun x : Real => x * Real.exp (-x)) (Set.Ici 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 1) (by fun_prop)
  intro x hx
  rw [interior_Ici] at hx
  change 1 < x at hx
  have hexp : HasDerivAt (fun y : Real => Real.exp (-y))
      (-Real.exp (-x)) x := by
    simpa using! (hasDerivAt_neg x).exp
  have hderiv : HasDerivAt (fun y : Real => y * Real.exp (-y))
      ((1 - x) * Real.exp (-x)) x := by
    simpa [sub_mul] using! (hasDerivAt_id x).mul hexp
  rw [hderiv.deriv]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hx) (Real.exp_pos _)

private abbrev Plane := EuclideanSpace Real (Fin 2)

private lemma isConnected_source_inter_preimage_sphere
    {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X Plane) {r R : Real}
    (hr : 0 ≤ r) (hrR : r < R)
    (hball : Metric.ball (0 : Plane) R ⊆ e.target) :
    IsConnected (e.source ∩ e ⁻¹' Metric.sphere (0 : Plane) r) := by
  have hsphereTarget : Metric.sphere (0 : Plane) r ⊆ e.target :=
    (Metric.sphere_subset_ball hrR).trans hball
  have himage : e.symm '' Metric.sphere (0 : Plane) r =
      e.source ∩ e ⁻¹' Metric.sphere (0 : Plane) r := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzTarget := hsphereTarget hz
      refine ⟨e.map_target hzTarget, ?_⟩
      change e (e.symm z) ∈ Metric.sphere (0 : Plane) r
      rw [e.right_inv hzTarget]
      exact hz
    · rintro ⟨hxsource, hxe⟩
      exact ⟨e x, hxe, e.left_inv hxsource⟩
  rw [← himage]
  have hrank : 1 < Module.rank Real Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num [Plane]
  exact (isConnected_sphere (E := Plane) hrank 0 hr).image
    e.symm (e.continuousOn_symm.mono hsphereTarget)

private lemma exists_gt_strictMonoOn_sub_const_mul_exp
    {c a : Real} (hc : 0 ≤ c) (ha : c * Real.exp a < 1) :
    ∃ T : Real, a < T ∧
      StrictMonoOn (fun s : Real => s - c * Real.exp s) (Set.Iic T) := by
  let U : Set Real := {s | c * Real.exp s < 1}
  have hUOpen : IsOpen U :=
    isOpen_lt (continuous_const.mul Real.continuous_exp) continuous_const
  have haU : a ∈ U := ha
  obtain ⟨l, u, ⟨hla, hau⟩, hlu⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hUOpen.mem_nhds haU)
  let T := (a + u) / 2
  have haT : a < T := by dsimp [T]; linarith
  have hTu : T < u := by dsimp [T]; linarith
  have hTU : T ∈ U := hlu ⟨lt_trans hla haT, hTu⟩
  refine ⟨T, haT, ?_⟩
  apply strictMonoOn_of_deriv_pos (convex_Iic T) (by fun_prop)
  intro x hx
  rw [interior_Iic] at hx
  change x < T at hx
  have hderiv : HasDerivAt (fun s : Real => s - c * Real.exp s)
      (1 - c * Real.exp x) x := by
    simpa using! (hasDerivAt_id x).sub ((Real.hasDerivAt_exp x).const_mul c)
  rw [hderiv.deriv]
  apply sub_pos.mpr
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (le_of_lt hx)) hc).trans_lt hTU

private lemma exists_lt_strictAntiOn_sub_const_mul_exp
    {c a : Real} (hc : 0 ≤ c) (ha : 1 < c * Real.exp a) :
    ∃ T : Real, T < a ∧
      StrictAntiOn (fun s : Real => s - c * Real.exp s) (Set.Ici T) := by
  let U : Set Real := {s | 1 < c * Real.exp s}
  have hUOpen : IsOpen U :=
    isOpen_lt continuous_const (continuous_const.mul Real.continuous_exp)
  have haU : a ∈ U := ha
  obtain ⟨l, u, ⟨hla, hau⟩, hlu⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hUOpen.mem_nhds haU)
  let T := (l + a) / 2
  have hlT : l < T := by dsimp [T]; linarith
  have hTa : T < a := by dsimp [T]; linarith
  have hTU : T ∈ U := hlu ⟨hlT, lt_trans hTa hau⟩
  refine ⟨T, hTa, ?_⟩
  apply strictAntiOn_of_deriv_neg (convex_Ici T) (by fun_prop)
  intro x hx
  rw [interior_Ici] at hx
  change T < x at hx
  have hderiv : HasDerivAt (fun s : Real => s - c * Real.exp s)
      (1 - c * Real.exp x) x := by
    simpa using! (hasDerivAt_id x).sub ((Real.hasDerivAt_exp x).const_mul c)
  rw [hderiv.deriv]
  apply sub_neg.mpr
  exact hTU.trans_le
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (le_of_lt hx)) hc)

private noncomputable def connectedComponentsEquivOfPairwiseDisjointOpenConnectedCover
    {X J : Type} [TopologicalSpace X] (U : J → Set X)
    (hopen : ∀ j, IsOpen (U j))
    (hdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (hcover : ⋃ j, U j = Set.univ)
    (hconn : ∀ j, IsConnected (U j)) :
    ConnectedComponents X ≃ J := by
  apply ConnectedComponents.equivOfIsClopenOfIsConnected _ hdisj hcover hconn
  intro j
  refine ⟨?_, hopen j⟩
  rw [← isOpen_compl_iff]
  have hcompl : (U j)ᶜ = ⋃ k : {k : J // k ≠ j}, U k := by
    ext x
    constructor
    · intro hx
      have hxcover : x ∈ ⋃ k, U k := by rw [hcover]; trivial
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxcover
      have hkj : k ≠ j := by
        intro hkj
        subst k
        exact hx hxk
      exact Set.mem_iUnion.mpr ⟨⟨k, hkj⟩, hxk⟩
    · rintro hx hxu
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
      exact Set.disjoint_left.mp (hdisj k.property) hxk hxu
  rw [hcompl]
  exact isOpen_iUnion fun k => hopen k

private lemma isConnected_of_image_subtype_val
    {X : Type} [TopologicalSpace X] {s : Set X} {U : Set s}
    (hU : IsConnected (Subtype.val '' U)) :
    IsConnected U := by
  refine ⟨?_, ?_⟩
  · exact Set.image_nonempty.mp hU.nonempty
  · exact Topology.IsInducing.subtypeVal.isPreconnected_image.mp hU.isPreconnected

private lemma sum_eq_zero_partitioned_by_equicardinal_predicates
    {X : Type} [Fintype X] (P Q : X → Prop)
    (e : {x : X // P x} ≃ {x : X // Q x})
    (hcover : ∀ x, P x ∨ Q x) (hdisj : ∀ x, ¬(P x ∧ Q x))
    (hPnonempty : Nonempty {x : X // P x})
    (F : X → Real) (A B : Real)
    (hPA : ∀ x, P x → F x = A) (hQB : ∀ x, Q x → F x = B)
    (hsum : ∑ x, F x = 0) :
    A + B = 0 := by
  classical
  have hQiff : ∀ x, Q x ↔ ¬P x := by
    intro x
    constructor
    · intro hxQ hxP
      exact hdisj x ⟨hxP, hxQ⟩
    · intro hxP
      exact (hcover x).resolve_left hxP
  have hcard : (Finset.univ.filter P).card =
      (Finset.univ.filter fun x => ¬P x).card := by
    calc
      (Finset.univ.filter P).card = Fintype.card {x : X // P x} := by
        simpa using (Fintype.card_subtype P).symm
      _ = Fintype.card {x : X // Q x} := Fintype.card_congr e
      _ = (Finset.univ.filter Q).card := by
        simpa using Fintype.card_subtype Q
      _ = (Finset.univ.filter fun x => ¬P x).card := by
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hQiff x
  have hsumP : ∑ x ∈ Finset.univ with P x, F x =
      (Finset.univ.filter P).card * A := by
    calc
      ∑ x ∈ Finset.univ with P x, F x =
          ∑ _x ∈ Finset.univ with P _x, A := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hPA x (Finset.mem_filter.mp hx).2
      _ = (Finset.univ.filter P).card * A := by simp
  have hsumNotP : ∑ x ∈ Finset.univ with ¬P x, F x =
      (Finset.univ.filter fun x => ¬P x).card * B := by
    calc
      ∑ x ∈ Finset.univ with ¬P x, F x =
          ∑ _x ∈ Finset.univ with ¬P _x, B := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hQB x ((hQiff x).2 (Finset.mem_filter.mp hx).2)
      _ = (Finset.univ.filter fun x => ¬P x).card * B := by simp
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ P F
  rw [hsumP, hsumNotP, ← hcard, hsum] at hsplit
  have hcardPos : 0 < (Finset.univ.filter P).card := by
    obtain ⟨x, hx⟩ := hPnonempty
    exact Finset.card_pos.mpr
      ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  have hcardReal : (0 : Real) < (Finset.univ.filter P).card := by
    exact_mod_cast hcardPos
  nlinarith

private lemma strictAntiOn_two_sub_mul_exp_sub_two_sub_mul_exp_neg_Iic_one :
    StrictAntiOn
      (fun x : Real => (2 - x) * Real.exp (x - 2) - x * Real.exp (-x))
      (Set.Iic 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Iic 1) (by fun_prop)
  intro x hx
  rw [interior_Iic] at hx
  change x < 1 at hx
  have hderivFirst : deriv
      (fun y : Real => (2 - y) * Real.exp (y - 2)) x =
      (1 - x) * Real.exp (x - 2) := by
    change deriv ((fun y : Real => 2 - y) * fun y : Real => Real.exp (y - 2)) x = _
    rw [deriv_mul (by fun_prop) (by fun_prop), deriv_const_sub_id,
      deriv_exp (by fun_prop), deriv_sub_const, deriv_id'']
    ring
  have hderivSecond : deriv
      (fun y : Real => y * Real.exp (-y)) x =
      (1 - x) * Real.exp (-x) := by
    have hexp : HasDerivAt (fun y : Real => Real.exp (-y))
        (-Real.exp (-x)) x := by
      simpa using! (hasDerivAt_neg x).exp
    have hmul := (hasDerivAt_id x).mul hexp
    change deriv (id * fun y : Real => Real.exp (-y)) x = _
    rw [hmul.deriv]
    simp only [id_eq]
    ring
  change deriv
    ((fun y : Real => (2 - y) * Real.exp (y - 2)) -
      fun y : Real => y * Real.exp (-y)) x < 0
  rw [deriv_sub (by fun_prop) (by fun_prop), hderivFirst, hderivSecond]
  rw [← mul_sub]
  apply mul_neg_of_pos_of_neg
  · exact sub_pos.mpr hx
  · exact sub_neg.mpr (Real.exp_lt_exp.mpr (by linarith))

theorem normalizedGradientRicciSoliton_metricScalarAt_ne_one_at_criticalPoint_of_finrank_eq_two_of_not_constant
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) (x : M)
    (hcrit : IsCriticalPointAt I f x) :
    metricScalarAt (I := I) (M := M) g x ≠ 1 := by
  intro hscalarx
  apply hnonconstant
  have hgradx : gradFun (I := I) g f x = 0 :=
    gradFun_eq_zero_of_mfderiv_eq_zero (I := I) g f hcrit
  have hf :=
    normalizedGradientRicciSoliton_potential_eq_one_of_finrank_eq_two_of_scalar_eq_one_of_gradient_eq_zero
      (I := I) h hdim x hscalarx hgradx
  intro y z
  rw [hf y, hf z]

theorem normalizedGradientRicciSoliton_isNondegenerateCriticalPointAt_of_finrank_eq_two_of_not_constant
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) (x : M)
    (hcrit : IsCriticalPointAt I f x) :
    IsNondegenerateCriticalPointAt I f x := by
  apply isNondegenerateCriticalPointAt_of_hessFun_eq_smul_metric
    (c := (1 - metricScalarAt (I := I) (M := M) g x) / 2) g f x hcrit
  · exact div_ne_zero
      (sub_ne_zero.mpr
        (normalizedGradientRicciSoliton_metricScalarAt_ne_one_at_criticalPoint_of_finrank_eq_two_of_not_constant
          (I := I) h hdim hnonconstant x hcrit).symm)
      (by norm_num)
  · intro v w
    exact normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
      (I := I) h hdim x v w

theorem normalizedGradientRicciSoliton_finite_criticalPoints_of_compact_of_finrank_eq_two_of_not_constant
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) :
    (criticalPoints I f).Finite :=
  finite_criticalPoints_of_compact_of_isNondegenerate f f.contMDiff fun p hp =>
    normalizedGradientRicciSoliton_isNondegenerateCriticalPointAt_of_finrank_eq_two_of_not_constant
      h hdim hnonconstant p hp

private theorem exists_local_regularized_gradient_flux_limit
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) (p : M)
    (hcrit : IsCriticalPointAt I f p) :
    ∃ U : Set M, U ∈ 𝓝 p ∧ ∀ b : M → Real,
      Continuous b → tsupport b ⊆ U →
        Tendsto
          (fun ε : Real => ∫ x,
            ε * (1 - metricScalarAt (I := I) (M := M) g x) * b x *
              (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2
                ∂riemannianVolumeMeasure (I := I) (M := M) g)
          (𝓝[>] 0)
          (𝓝 (4 * Real.pi /
            (1 - metricScalarAt (I := I) (M := M) g p) * b p)) := by
  let R : M → Real := fun x => metricScalarAt (I := I) (M := M) g x
  have hRne : R p ≠ 1 :=
    normalizedGradientRicciSoliton_metricScalarAt_ne_one_at_criticalPoint_of_finrank_eq_two_of_not_constant
      (I := I) h hdim hnonconstant p hcrit
  have hc : (1 - R p) / 2 ≠ 0 := by
    intro hzero
    apply hRne
    linarith
  obtain ⟨U, hU, hlim⟩ :=
    exists_nhds_tendsto_integral_regularized_normGradSqFun_inv_sq_mul_of_hessFun_eq_smul_metric_of_finrank_eq_two
      (I := I) hdim g f p hcrit hc
        (normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
          (I := I) h hdim p)
  refine ⟨U, hU, ?_⟩
  intro b hb hbU
  let B : M → Real := fun x => (1 - R x) * b x
  have hB : Continuous B :=
    (continuous_const.sub (metricScalar_smooth (I := I) (M := M) g).continuous).mul hb
  have hBSupport : tsupport B ⊆ U :=
    tsupport_mul_subset_right.trans hbU
  have ht := hlim B hB hBSupport
  have hlimit :
      Real.pi / ((1 - R p) / 2) ^ 2 * B p =
        4 * Real.pi / (1 - R p) * b p := by
    dsimp only [B]
    field_simp [sub_ne_zero.mpr hRne.symm]
    ring
  rw [hlimit] at ht
  simpa only [B, R, mul_assoc] using ht

omit [I.Boundaryless] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ConnectedSpace M] in
private theorem exists_finite_bumps
    {s : Set M} (hs : s.Finite)
    (U : ↥hs.toFinset → Set M)
    (hU : ∀ p : ↥hs.toFinset, U p ∈ 𝓝 (p : M)) :
    ∃ χ : ∀ p : ↥hs.toFinset, SmoothBumpFunction I (p : M),
      (∀ p, tsupport (χ p : M → Real) ⊆ U p) ∧
      ∀ q ∈ s,
        (fun x : M => 1 - ∑ p : ↥hs.toFinset, (χ p : M → Real) x) =ᶠ[𝓝 q] 0 := by
  classical
  have hnhds : ∀ p : ↥hs.toFinset,
      U p ∩ (s \ {(p : M)})ᶜ ∈ 𝓝 (p : M) := by
    intro p
    apply inter_mem (hU p)
    apply hs.sdiff.isClosed.isOpen_compl.mem_nhds
    exact fun hp => hp.2 rfl
  have hbump : ∀ p : ↥hs.toFinset,
      ∃ χ : SmoothBumpFunction I (p : M),
        tsupport (χ : M → Real) ⊆ U p ∩ (s \ {(p : M)})ᶜ := by
    intro p
    obtain ⟨χ, _, hχ⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := I) (p : M)).mem_iff.mp
        (hnhds p)
    exact ⟨χ, hχ⟩
  choose χ hχ using hbump
  refine ⟨χ, fun p => (hχ p).trans inter_subset_left, ?_⟩
  intro q hq
  let q' : ↥hs.toFinset := ⟨q, hs.mem_toFinset.mpr hq⟩
  have hnear : ∀ p : ↥hs.toFinset,
      ∀ᶠ x in 𝓝 q, (χ p : M → Real) x = if p = q' then 1 else 0 := by
    intro p
    by_cases hp : p = q'
    · subst p
      filter_upwards [(χ q').eventuallyEq_one] with x hx
      simpa only [if_pos, Pi.one_apply] using hx
    · have hqNotSupport : q ∉ tsupport (χ p : M → Real) := by
        intro hqSupport
        have hqAvoid := (hχ p hqSupport).2
        apply hqAvoid
        refine ⟨hq, ?_⟩
        intro hqp
        apply hp
        apply Subtype.ext
        simpa only [q'] using hqp.symm
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hqNotSupport] with x hx
      simpa only [hp, if_false, Pi.zero_apply] using hx
  have hall : ∀ᶠ x in 𝓝 q, ∀ p ∈ (Finset.univ : Finset ↥hs.toFinset),
      (χ p : M → Real) x = if p = q' then 1 else 0 :=
    (eventually_all_finset (Finset.univ : Finset ↥hs.toFinset)).2
      (fun p _ => hnear p)
  filter_upwards [hall] with x hx
  have hsum : (∑ p : ↥hs.toFinset, (χ p : M → Real) x) =
      ∑ p : ↥hs.toFinset, if p = q' then 1 else 0 :=
    Finset.sum_congr rfl fun p hp => hx p hp
  rw [hsum]
  simp

private theorem sum_regularized_gradient_flux_at_criticalPoints_eq_zero
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z)
    (hfinite : (criticalPoints I f).Finite) :
    (∑ p : ↥hfinite.toFinset,
      4 * Real.pi /
        (1 - metricScalarAt (I := I) (M := M) g (p : M))) = 0 := by
  classical
  let C := hfinite.toFinset
  let R : M → Real := fun x => metricScalarAt (I := I) (M := M) g x
  let μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  have hlocal : ∀ p : ↥C, ∃ U : Set M, U ∈ 𝓝 (p : M) ∧
      ∀ b : M → Real, Continuous b → tsupport b ⊆ U →
        Tendsto
          (fun ε : Real => ∫ x,
            ε * (1 - R x) * b x *
              (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2 ∂μ)
          (𝓝[>] 0) (𝓝 (4 * Real.pi / (1 - R p) * b p)) := by
    intro p
    have hpcrit : (p : M) ∈ criticalPoints I f := by
      exact hfinite.mem_toFinset.mp p.property
    simpa only [R, μ] using
      exists_local_regularized_gradient_flux_limit
        (I := I) h hdim hnonconstant (p : M) hpcrit
  choose U hU hlimit using hlocal
  obtain ⟨χ, hχSupport, hχNear⟩ :=
    exists_finite_bumps (I := I) hfinite U hU
  let φ : M → Real := fun x => ∑ p : ↥C, (χ p : M → Real) x
  let B : M → Real := fun x => (1 - R x) * (1 - φ x)
  let s : Set M := tsupport B
  let localIntegral : ↥C → Real → Real := fun p ε => ∫ x,
    ε * (1 - R x) * (χ p : M → Real) x *
      (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2 ∂μ
  let remainderIntegral : Real → Real := fun ε => ∫ x in s,
    (ε * (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2) • B x ∂μ
  have hφContinuous : Continuous φ := by
    exact continuous_finsetSum Finset.univ fun p _ => (χ p).continuous
  have hBContinuous : Continuous B := by
    exact (continuous_const.sub
      (metricScalar_smooth (I := I) (M := M) g).continuous).mul
        (continuous_const.sub hφContinuous)
  have hsCompact : IsCompact s := by
    exact (isClosed_tsupport B).isCompact
  have hsDisjoint : Disjoint s (criticalPoints I f) := by
    rw [Set.disjoint_left]
    intro x hxs hxcrit
    have hnear : ∀ᶠ y in 𝓝 x, B y = 0 := by
      filter_upwards [hχNear x hxcrit] with y hy
      change 1 - ∑ p, (χ p : M → Real) y = 0 at hy
      change (1 - R y) * (1 - ∑ p, (χ p : M → Real) y) = 0
      rw [hy, mul_zero]
    have hxNotSupport : x ∉ tsupport B :=
      notMem_tsupport_iff_eventuallyEq.mpr (by
        filter_upwards [hnear] with y hy
        simpa only [Pi.zero_apply] using hy)
    exact hxNotSupport hxs
  have hBIntegrable : Integrable B μ := by
    exact DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hBContinuous (HasCompactSupport.of_compactSpace B)
  have hremTendsto : Tendsto remainderIntegral (𝓝[>] 0) (𝓝 0) := by
    simpa only [remainderIntegral, μ] using
      tendsto_setIntegral_regularized_normGradSqFun_inv_sq_smul_of_compact_of_disjoint_criticalPoints
        (I := I) hsCompact g f hsDisjoint hBIntegrable.integrableOn
  have hlocalTendsto : ∀ p : ↥C,
      Tendsto (localIntegral p) (𝓝[>] 0)
        (𝓝 (4 * Real.pi / (1 - R p))) := by
    intro p
    simpa only [localIntegral, SmoothBumpFunction.eq_one, mul_one] using
      hlimit p (χ p : M → Real) (χ p).continuous (hχSupport p)
  have hsumTendsto : Tendsto
      (fun ε => ∑ p : ↥C, localIntegral p ε) (𝓝[>] 0)
      (𝓝 (∑ p : ↥C, 4 * Real.pi / (1 - R p))) :=
    tendsto_finsetSum Finset.univ fun p _ => hlocalTendsto p
  have hsumEqNegRemainder : ∀ᶠ ε in 𝓝[>] (0 : Real),
      (∑ p : ↥C, localIntegral p ε) = -remainderIntegral ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < ε at hε
    have hdenNe : ∀ x : M,
        normGradSqFun (I := I) g f x + ε ≠ 0 := by
      intro x
      exact ne_of_gt (add_pos_of_nonneg_of_pos
        (normGradSqFun_nonneg (I := I) g f x) hε)
    have hdenContinuous : Continuous
        (fun x : M => (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2) :=
      ((normGradSqFun_continuous (I := I) g f.contMDiff).add
        continuous_const).inv₀ hdenNe |>.pow 2
    let A : ↥C → M → Real := fun p x =>
      ε * (1 - R x) * (χ p : M → Real) x *
        (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2
    let D : M → Real := fun x =>
      (ε * (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2) • B x
    have hAIntegrable : ∀ p ∈ (Finset.univ : Finset ↥C), Integrable (A p) μ := by
      intro p _
      apply DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
        (I := I) g
      · exact (((continuous_const.mul
          (continuous_const.sub
            (metricScalar_smooth (I := I) (M := M) g).continuous)).mul
              (χ p).continuous).mul hdenContinuous)
      · exact HasCompactSupport.of_compactSpace (A p)
    have hASumIntegrable : Integrable (fun x => ∑ p : ↥C, A p x) μ :=
      integrable_finsetSum Finset.univ hAIntegrable
    have hDContinuous : Continuous D := by
      exact (continuous_const.mul hdenContinuous).smul hBContinuous
    have hDIntegrable : Integrable D μ := by
      exact DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
        (I := I) g hDContinuous (HasCompactSupport.of_compactSpace D)
    have hdecomp :
        (∑ p : ↥C, localIntegral p ε) + ∫ x, D x ∂μ =
          ∫ x, ε * (1 - R x) *
            (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2 ∂μ := by
      change (∑ p ∈ (Finset.univ : Finset ↥C), ∫ x, A p x ∂μ) +
          ∫ x, D x ∂μ = _
      rw [← MeasureTheory.integral_finsetSum Finset.univ hAIntegrable,
        ← integral_add hASumIntegrable hDIntegrable]
      apply integral_congr_ae
      filter_upwards with x
      calc
        (∑ p : ↥C, A p x) + D x =
            ε * (1 - R x) * (∑ p : ↥C, (χ p : M → Real) x) *
                (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2 + D x := by
          congr 1
          simp only [A]
          rw [← Finset.sum_mul]
          congr 1
          rw [← Finset.mul_sum]
        _ = ε * (1 - R x) *
            (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2 := by
          simp only [D, B, φ, smul_eq_mul]
          ring
    have hglobal :=
      normalizedGradientRicciSoliton_regularized_gradient_integral_eq_zero
        (I := I) h hdim ε hε
    have hdecompZero : (∑ p : ↥C, localIntegral p ε) + ∫ x, D x ∂μ = 0 := by
      rw [hdecomp]
      simpa only [R, μ] using hglobal
    have hremEq : ∫ x, D x ∂μ = remainderIntegral ε := by
      simp only [remainderIntegral]
      rw [← integral_indicator hsCompact.measurableSet]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ s
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx]
        have hBx : B x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp only [D, hBx, smul_zero]
    rw [hremEq] at hdecompZero
    exact eq_neg_of_add_eq_zero_left hdecompZero
  have hsumTendstoZero : Tendsto
      (fun ε => ∑ p : ↥C, localIntegral p ε) (𝓝[>] 0) (𝓝 0) := by
    have hneg := hremTendsto.neg
    have heq :
        (fun ε => ∑ p : ↥C, localIntegral p ε) =ᶠ[𝓝[>] 0]
          (fun ε => -remainderIntegral ε) := hsumEqNegRemainder
    simpa only [neg_zero] using hneg.congr' heq.symm
  have hsumZero : (∑ p : ↥C, 4 * Real.pi / (1 - R p)) = 0 :=
    tendsto_nhds_unique hsumTendsto hsumTendstoZero
  simpa only [C, R] using hsumZero

theorem normalizedGradientRicciSoliton_metricScalarAt_lt_one_at_local_min_of_finrank_eq_two_of_not_constant
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) (x : M)
    (hmin : IsLocalMin f x) :
    metricScalarAt (I := I) (M := M) g x < 1 := by
  have hgradx : gradFun (I := I) g f x = 0 := by
    exact gradientFun_eq_zero_of_isLocalMin (I := I) g hmin
      ((f.contMDiff x).mdifferentiableAt (by simp))
  have hscalarNe : metricScalarAt (I := I) (M := M) g x ≠ 1 := by
    intro hscalarx
    apply hnonconstant
    have hf :=
      normalizedGradientRicciSoliton_potential_eq_one_of_finrank_eq_two_of_scalar_eq_one_of_gradient_eq_zero
        (I := I) h hdim x hscalarx hgradx
    intro y z
    rw [hf y, hf z]
  have hfinrank : Module.finrank Real (TangentSpace I x) = 2 := by
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  let _ : Nontrivial (TangentSpace I x) :=
    Module.nontrivial_of_finrank_pos (by rw [hfinrank]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace I x)
  have hhess := hessFun_apply_self_nonneg_at_spatial_min
    (I := I) g hmin f.contMDiff v
  rw [normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
    (I := I) h hdim x v v] at hhess
  have hinner : 0 < g.inner x v v := g.pos x v hv
  have hle : metricScalarAt (I := I) (M := M) g x ≤ 1 := by
    nlinarith
  exact lt_of_le_of_ne hle hscalarNe

theorem normalizedGradientRicciSoliton_one_lt_metricScalarAt_at_local_max_of_finrank_eq_two_of_not_constant
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) (x : M)
    (hmax : IsLocalMax f x) :
    1 < metricScalarAt (I := I) (M := M) g x := by
  have hgradx : gradFun (I := I) g f x = 0 := by
    exact gradientFun_eq_zero_of_isLocalMax (I := I) g hmax
      ((f.contMDiff x).mdifferentiableAt (by simp))
  have hscalarNe : metricScalarAt (I := I) (M := M) g x ≠ 1 := by
    intro hscalarx
    apply hnonconstant
    have hf :=
      normalizedGradientRicciSoliton_potential_eq_one_of_finrank_eq_two_of_scalar_eq_one_of_gradient_eq_zero
        (I := I) h hdim x hscalarx hgradx
    intro y z
    rw [hf y, hf z]
  have hfinrank : Module.finrank Real (TangentSpace I x) = 2 := by
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  let _ : Nontrivial (TangentSpace I x) :=
    Module.nontrivial_of_finrank_pos (by rw [hfinrank]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace I x)
  have hhess := hessFun_apply_self_nonpos_at_spatial_max
    (I := I) g hmax f.contMDiff v
  rw [normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
    (I := I) h hdim x v v] at hhess
  have hinner : 0 < g.inner x v v := g.pos x v hv
  have hle : 1 ≤ metricScalarAt (I := I) (M := M) g x := by
    nlinarith
  exact lt_of_le_of_ne hle hscalarNe.symm

theorem normalizedGradientRicciSoliton_exists_potential_extrema_with_scalar_lt_one_and_one_lt_of_compact_of_finrank_eq_two_of_not_constant
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) :
    ∃ xmin xmax : M,
      IsMinOn f univ xmin ∧ IsMaxOn f univ xmax ∧
      metricScalarAt (I := I) (M := M) g xmin < 1 ∧
      1 < metricScalarAt (I := I) (M := M) g xmax := by
  obtain ⟨xmin, _, hmin⟩ :=
    (isCompact_univ : IsCompact (univ : Set M)).exists_isMinOn
      univ_nonempty f.contMDiff.continuous.continuousOn
  obtain ⟨xmax, _, hmax⟩ :=
    (isCompact_univ : IsCompact (univ : Set M)).exists_isMaxOn
      univ_nonempty f.contMDiff.continuous.continuousOn
  refine ⟨xmin, xmax, hmin, hmax, ?_, ?_⟩
  · exact
      normalizedGradientRicciSoliton_metricScalarAt_lt_one_at_local_min_of_finrank_eq_two_of_not_constant
        (I := I) h hdim hnonconstant xmin (hmin.isLocalMin (by simp))
  · exact
      normalizedGradientRicciSoliton_one_lt_metricScalarAt_at_local_max_of_finrank_eq_two_of_not_constant
        (I := I) h hdim hnonconstant xmax (hmax.isLocalMax (by simp))

private theorem normalizedGradientRicciSoliton_critical_scalar_eq_extreme_scalar
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z)
    {xmin xmax p : M}
    (hmin : IsMinOn f univ xmin) (hmax : IsMaxOn f univ xmax)
    (hpcrit : IsCriticalPointAt I f p) :
    metricScalarAt (I := I) (M := M) g p =
        metricScalarAt (I := I) (M := M) g xmin ∨
      metricScalarAt (I := I) (M := M) g p =
        metricScalarAt (I := I) (M := M) g xmax := by
  let R : M → Real := fun x => metricScalarAt (I := I) (M := M) g x
  have hgradp : gradFun (I := I) g f p = 0 :=
    gradFun_eq_zero_of_mfderiv_eq_zero (I := I) g f hpcrit
  have hgradMin : gradFun (I := I) g f xmin = 0 :=
    gradientFun_eq_zero_of_isLocalMin (I := I) g
      (hmin.isLocalMin (by simp)) ((f.contMDiff xmin).mdifferentiableAt (by simp))
  have hgradMax : gradFun (I := I) g f xmax = 0 :=
    gradientFun_eq_zero_of_isLocalMax (I := I) g
      (hmax.isLocalMax (by simp)) ((f.contMDiff xmax).mdifferentiableAt (by simp))
  have hRmin : R xmin < 1 :=
    normalizedGradientRicciSoliton_metricScalarAt_lt_one_at_local_min_of_finrank_eq_two_of_not_constant
      (I := I) h hdim hnonconstant xmin (hmin.isLocalMin (by simp))
  have hRmax : 1 < R xmax :=
    normalizedGradientRicciSoliton_one_lt_metricScalarAt_at_local_max_of_finrank_eq_two_of_not_constant
      (I := I) h hdim hnonconstant xmax (hmax.isLocalMax (by simp))
  have hRpne : R p ≠ 1 :=
    normalizedGradientRicciSoliton_metricScalarAt_ne_one_at_criticalPoint_of_finrank_eq_two_of_not_constant
      (I := I) h hdim hnonconstant p hpcrit
  have hEqMin : R p * Real.exp (-R p) = R xmin * Real.exp (-R xmin) :=
    normalizedGradientRicciSoliton_metricScalarAt_mul_exp_neg_eq_of_finrank_eq_two_of_gradient_eq_zero
      (I := I) h hdim p xmin hgradp hgradMin
  have hEqMax : R p * Real.exp (-R p) = R xmax * Real.exp (-R xmax) :=
    normalizedGradientRicciSoliton_metricScalarAt_mul_exp_neg_eq_of_finrank_eq_two_of_gradient_eq_zero
      (I := I) h hdim p xmax hgradp hgradMax
  rcases lt_or_gt_of_ne hRpne with hRp | hRp
  · left
    apply strictMonoOn_mul_exp_neg_Iic_one.injOn
    · exact le_of_lt hRp
    · exact le_of_lt hRmin
    · exact hEqMin
  · right
    apply strictAntiOn_mul_exp_neg_Ici_one.injOn
    · exact le_of_lt hRp
    · exact le_of_lt hRmax
    · exact hEqMax

theorem normalizedGradientRicciSoliton_isMinOn_or_isMaxOn_at_criticalPoint_of_compact_of_finrank_eq_two_of_not_constant
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z)
    (p : M) (hpcrit : IsCriticalPointAt I f p) :
    IsMinOn f univ p ∨ IsMaxOn f univ p := by
  obtain ⟨xmin, xmax, hmin, hmax, _, _⟩ :=
    normalizedGradientRicciSoliton_exists_potential_extrema_with_scalar_lt_one_and_one_lt_of_compact_of_finrank_eq_two_of_not_constant
      (I := I) h hdim hnonconstant
  have hscalar :=
    normalizedGradientRicciSoliton_critical_scalar_eq_extreme_scalar
      (I := I) h hdim hnonconstant hmin hmax hpcrit
  have hgradp : gradFun (I := I) g f p = 0 :=
    gradFun_eq_zero_of_mfderiv_eq_zero (I := I) g f hpcrit
  have hgradMin : gradFun (I := I) g f xmin = 0 :=
    gradientFun_eq_zero_of_isLocalMin (I := I) g
      (hmin.isLocalMin (by simp)) ((f.contMDiff xmin).mdifferentiableAt (by simp))
  have hgradMax : gradFun (I := I) g f xmax = 0 :=
    gradientFun_eq_zero_of_isLocalMax (I := I) g
      (hmax.isLocalMax (by simp)) ((f.contMDiff xmax).mdifferentiableAt (by simp))
  have hfp :=
    normalizedGradientRicciSoliton_potential_eq_metricScalarAt_of_gradient_eq_zero
      (I := I) h p hgradp
  rcases hscalar with hscalar | hscalar
  · left
    have hfmin :=
      normalizedGradientRicciSoliton_potential_eq_metricScalarAt_of_gradient_eq_zero
        (I := I) h xmin hgradMin
    have hfpmin : f p = f xmin := hfp.trans (hscalar.trans hfmin.symm)
    intro x hx
    rw [hfpmin]
    exact hmin hx
  · right
    have hfmax :=
      normalizedGradientRicciSoliton_potential_eq_metricScalarAt_of_gradient_eq_zero
        (I := I) h xmax hgradMax
    have hfpmax : f p = f xmax := hfp.trans (hscalar.trans hfmax.symm)
    intro x hx
    rw [hfpmax]
    exact hmax hx

private theorem exists_low_regular_level_components_equiv_minima
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z)
    {xmin xmax : M} (hmin : IsMinOn f univ xmin)
    (hmax : IsMaxOn f univ xmax) :
    ∃ a : Real, f xmin < a ∧ a < (f xmin + f xmax) / 2 ∧
      Nonempty (ConnectedComponents (f ⁻¹' {a}) ≃
        {p : M // IsMinOn f univ p}) := by
  let _ : NeZero (Module.finrank Real E) := ⟨by omega⟩
  let P : Set M := {p | IsMinOn f univ p}
  have hfinite :=
    normalizedGradientRicciSoliton_finite_criticalPoints_of_compact_of_finrank_eq_two_of_not_constant
      (I := I) h hdim hnonconstant
  have hPcritical : P ⊆ criticalPoints I f := by
    intro p hp
    exact mfderiv_eq_zero_at_spatial_min (I := I)
      (hp.isLocalMin (by simp)) ((f.contMDiff p).mdifferentiableAt (by simp))
  have hPfinite : P.Finite := hfinite.subset hPcritical
  let _ : Fintype P := hPfinite.fintype
  obtain ⟨V, hV, hVdisj⟩ := hfinite.t2_separation
  obtain ⟨c, hc⟩ :=
    normalizedGradientRicciSoliton_exists_scalar_eq_const_mul_exp_of_finrank_eq_two
      (I := I) h hdim
  have hc0 : 0 ≤ c := by
    have hR := normalizedGradientRicciSoliton_scalar_nonneg (I := I) h xmin
    rw [hc xmin] at hR
    rw [mul_comm] at hR
    exact nonneg_of_mul_nonneg_right hR (Real.exp_pos _)
  let q : Real → Real := fun s => s - c * Real.exp s
  have hlocal : ∀ p : P, ∃ T : Real, f xmin < T ∧
      StrictMonoOn q (Set.Iic T) ∧
      ∃ e : OpenPartialHomeomorph M Plane,
        (p : M) ∈ e.source ∧ e p = 0 ∧
        (∀ x ∈ e.source, ‖e x‖ ^ 2 = normGradSqFun (I := I) g f x) ∧
        e.source ⊆ V p ∧ ∀ x ∈ e.source, f x < T := by
    intro p
    have hpmin : IsMinOn f univ p := p.property
    have hfp : f p = f xmin :=
      le_antisymm (hpmin (by simp)) (hmin (by simp))
    have hscalarLt :=
      normalizedGradientRicciSoliton_metricScalarAt_lt_one_at_local_min_of_finrank_eq_two_of_not_constant
        (I := I) h hdim hnonconstant p (hpmin.isLocalMin (by simp))
    have hRlt := hscalarLt
    rw [hc p] at hRlt
    obtain ⟨T, hpT, hmono⟩ :=
      exists_gt_strictMonoOn_sub_const_mul_exp hc0 hRlt
    have hpcrit : IsCriticalPointAt I f p := hPcritical p.property
    have hcoef :
        (1 - metricScalarAt (I := I) (M := M) g p) / 2 ≠ 0 := by
      exact div_ne_zero (sub_ne_zero.mpr (ne_of_gt hscalarLt)) (by norm_num)
    obtain ⟨e0, hpe0, he0p, he0norm⟩ :=
      exists_openPartialHomeomorph_norm_sq_eq_normGradSqFun_of_hessFun_eq_smul_metric_of_finrank_eq_two
        (I := I) hdim g f p hpcrit hcoef
          (normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
            (I := I) h hdim p)
    let W : Set M := V p ∩ f ⁻¹' Set.Iio T
    have hWopen : IsOpen W :=
      (hV p).2.inter (isOpen_Iio.preimage f.contMDiff.continuous)
    let e : OpenPartialHomeomorph M Plane := e0.restrOpen W hWopen
    have hpe : (p : M) ∈ e.source := by
      change (p : M) ∈ e0.source ∩ W
      refine ⟨hpe0, (hV p).1, ?_⟩
      exact hpT
    have hxminT : f xmin < T := by rw [← hfp]; exact hpT
    refine ⟨T, hxminT, hmono, e, hpe, ?_, ?_, ?_, ?_⟩
    · simpa only [e, OpenPartialHomeomorph.coe_restrOpen] using he0p
    · intro x hx
      apply he0norm x
      change x ∈ e0.source ∩ W at hx
      exact hx.1
    · intro x hx
      change x ∈ e0.source ∩ W at hx
      exact hx.2.1
    · intro x hx
      change x ∈ e0.source ∩ W at hx
      exact hx.2.2
  choose T hminT hmono e hpe hep hnorm hsourceV hfT using hlocal
  have hlocalBall : ∀ p : P, ∃ R : Real, 0 < R ∧
      Metric.ball (0 : Plane) R ⊆ (e p).target := by
    intro p
    have hzeroTarget : (0 : Plane) ∈ (e p).target := by
      rw [← hep p]
      exact (e p).map_source (hpe p)
    exact Metric.mem_nhds_iff.mp ((e p).open_target.mem_nhds hzeroTarget)
  choose R hRpos hball using hlocalBall
  have hminmax : f xmin < f xmax := by
    have hle : f xmin ≤ f xmax := hmin (by simp)
    apply lt_of_le_of_ne hle
    intro heq
    apply hnonconstant
    intro y z
    apply le_antisymm
    · calc
        f y ≤ f xmax := hmax (by simp)
        _ = f xmin := heq.symm
        _ ≤ f z := hmin (by simp)
    · calc
        f z ≤ f xmax := hmax (by simp)
        _ = f xmin := heq.symm
        _ ≤ f y := hmin (by simp)
  have hqgrad : ∀ x : M,
      q (f x) = normGradSqFun (I := I) g f x := by
    intro x
    dsimp only [q]
    rw [← hc x]
    linarith [h.2.2 x]
  have hgradMin : gradFun (I := I) g f xmin = 0 :=
    gradientFun_eq_zero_of_isLocalMin (I := I) g
      (hmin.isLocalMin (by simp)) ((f.contMDiff xmin).mdifferentiableAt (by simp))
  have hqzero : q (f xmin) = 0 := by
    rw [hqgrad xmin]
    simp only [normGradSqFun_def, hgradMin, map_zero]
  let O : Set M := ⋃ p : P, (e p).source
  have hOopen : IsOpen O := isOpen_iUnion fun p => (e p).open_source
  let K : Set M := Oᶜ
  have hKcompact : IsCompact K := hOopen.isClosed_compl.isCompact
  have hfKcompact : IsCompact (f '' K) :=
    hKcompact.image f.contMDiff.continuous
  have hminNotImage : f xmin ∉ f '' K := by
    rintro ⟨x, hxK, hfx⟩
    have hxmin : IsMinOn f univ x := by
      intro y hy
      rw [hfx]
      exact hmin hy
    let p : P := ⟨x, hxmin⟩
    have hxO : x ∈ O := Set.mem_iUnion.mpr ⟨p, hpe p⟩
    exact hxK hxO
  have havoid : (f '' K)ᶜ ∈ nhds (f xmin) :=
    hfKcompact.isClosed.isOpen_compl.mem_nhds hminNotImage
  have hbelowMid : {s : Real | s < (f xmin + f xmax) / 2} ∈ nhds (f xmin) :=
    isOpen_Iio.mem_nhds (by
      change f xmin < (f xmin + f xmax) / 2
      linarith [hminmax])
  have hbelowT : ∀ p : P, {s : Real | s < T p} ∈ nhds (f xmin) := by
    intro p
    exact isOpen_Iio.mem_nhds (hminT p)
  have hbelowTAll : ∀ᶠ s in nhds (f xmin), ∀ p : P, s < T p := by
    have hall :=
      (eventually_all_finset (Finset.univ : Finset P)).2
        (fun p _ => hbelowT p)
    simpa only [Finset.mem_univ, forall_const] using hall
  have hqcontinuous : Continuous q :=
    continuous_id.sub (continuous_const.mul Real.continuous_exp)
  have hbelowRadius : ∀ p : P,
      {s : Real | q s < (R p) ^ 2} ∈ nhds (f xmin) := by
    intro p
    have hmem : Set.Iio ((R p) ^ 2) ∈ nhds (q (f xmin)) := by
      apply isOpen_Iio.mem_nhds
      change q (f xmin) < (R p) ^ 2
      rw [hqzero]
      exact sq_pos_of_pos (hRpos p)
    change q ⁻¹' Set.Iio ((R p) ^ 2) ∈ nhds (f xmin)
    exact hqcontinuous.continuousAt hmem
  have hbelowRadiusAll :
      ∀ᶠ s in nhds (f xmin), ∀ p : P, q s < (R p) ^ 2 := by
    have hall :=
      (eventually_all_finset (Finset.univ : Finset P)).2
        (fun p _ => hbelowRadius p)
    simpa only [Finset.mem_univ, forall_const] using hall
  have hgood : {s : Real |
      s < (f xmin + f xmax) / 2 ∧ (∀ p : P, s < T p) ∧
        (∀ p : P, q s < (R p) ^ 2) ∧ s ∉ f '' K} ∈ nhds (f xmin) := by
    filter_upwards [hbelowMid, hbelowTAll, hbelowRadiusAll, havoid] with s hsmid hsT hsR hsK
    exact ⟨hsmid, hsT, hsR, hsK⟩
  obtain ⟨l, u, hminIoo, hIoo⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hgood
  let a : Real := (f xmin + u) / 2
  have haIoo : a ∈ Set.Ioo l u := by
    dsimp only [a]
    constructor <;> linarith [hminIoo.1, hminIoo.2]
  have haGood := hIoo haIoo
  have hmina : f xmin < a := by
    dsimp only [a]
    linarith [hminIoo.2]
  have hqapos : 0 < q a := by
    have hstrict := hmono (⟨xmin, hmin⟩ : P)
      (le_of_lt (hminT ⟨xmin, hmin⟩))
      (le_of_lt (haGood.2.1 ⟨xmin, hmin⟩)) hmina
    rwa [hqzero] at hstrict
  have hlevelCover : f ⁻¹' {a} ⊆ O := by
    intro x hx
    by_contra hxO
    apply haGood.2.2.2
    exact ⟨x, hxO, by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx⟩
  let r : Real := Real.sqrt (q a)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = q a := by
    exact Real.sq_sqrt (le_of_lt hqapos)
  have hrR : ∀ p : P, r < R p := by
    intro p
    have hrnonneg : 0 ≤ r := Real.sqrt_nonneg _
    nlinarith [haGood.2.2.1 p, hRpos p]
  let L : Set M := f ⁻¹' {a}
  let U : P → Set L := fun p => {x | (x : M) ∈ (e p).source}
  have hUopen : ∀ p : P, IsOpen (U p) := by
    intro p
    exact (e p).open_source.preimage continuous_subtype_val
  have hUdisj : Pairwise fun p z : P => Disjoint (U p) (U z) := by
    intro p z hpz
    rw [Set.disjoint_left]
    intro x hxp hxz
    have hpzM : (p : M) ≠ (z : M) := fun hpz' => hpz (Subtype.ext hpz')
    exact Set.disjoint_left.mp
      (hVdisj (hPcritical p.property) (hPcritical z.property) hpzM)
      (hsourceV p hxp) (hsourceV z hxz)
  have hUcover : ⋃ p : P, U p = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hxO : (x : M) ∈ O := hlevelCover x.property
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hxO
    exact Set.mem_iUnion.mpr ⟨p, hxp⟩
  have hUconn : ∀ p : P, IsConnected (U p) := by
    intro p
    apply isConnected_of_image_subtype_val
    have himage : Subtype.val '' U p =
        (e p).source ∩ (e p) ⁻¹' Metric.sphere (0 : Plane) r := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hlevel : f (y : M) = a := by
          simpa only [L, Set.mem_preimage, Set.mem_singleton_iff] using y.property
        have hnormsq : ‖e p y‖ ^ 2 = q a := by
          calc
            ‖e p y‖ ^ 2 = normGradSqFun (I := I) g f y := hnorm p y hy
            _ = q (f y) := (hqgrad y).symm
            _ = q a := by rw [hlevel]
        have hnormeq : ‖e p y‖ = r := by
          nlinarith [norm_nonneg (e p y), hr0]
        exact ⟨hy, by
          change dist (e p y) 0 = r
          simpa only [dist_zero_right] using hnormeq⟩
      · rintro ⟨hxsource, hxsphere⟩
        have hnormeq : ‖e p x‖ = r := by
          change dist (e p x) 0 = r at hxsphere
          simpa only [dist_zero_right] using hxsphere
        have hqeq : q (f x) = q a := by
          calc
            q (f x) = normGradSqFun (I := I) g f x := hqgrad x
            _ = ‖e p x‖ ^ 2 := (hnorm p x hxsource).symm
            _ = r ^ 2 := by rw [hnormeq]
            _ = q a := hrsq
        have hfx : f x = a := by
          apply (hmono p).injOn
          · exact le_of_lt (hfT p x hxsource)
          · exact le_of_lt (haGood.2.1 p)
          · exact hqeq
        let y : L := ⟨x, by
          change f x ∈ ({a} : Set Real)
          simpa only [Set.mem_singleton_iff] using hfx⟩
        exact ⟨y, hxsource, rfl⟩
    rw [himage]
    exact isConnected_source_inter_preimage_sphere
      (e p) hr0 (hrR p) (hball p)
  let componentEquiv : ConnectedComponents L ≃ P :=
    connectedComponentsEquivOfPairwiseDisjointOpenConnectedCover
      U hUopen hUdisj hUcover hUconn
  refine ⟨a, hmina, haGood.1, ?_⟩
  change Nonempty (ConnectedComponents L ≃ P)
  exact ⟨componentEquiv⟩

private theorem exists_high_regular_level_components_equiv_maxima
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z)
    {xmin xmax : M} (hmin : IsMinOn f univ xmin)
    (hmax : IsMaxOn f univ xmax) :
    ∃ b : Real, (f xmin + f xmax) / 2 < b ∧ b < f xmax ∧
      Nonempty (ConnectedComponents (f ⁻¹' {b}) ≃
        {p : M // IsMaxOn f univ p}) := by
  let _ : NeZero (Module.finrank Real E) := ⟨by omega⟩
  let P : Set M := {p | IsMaxOn f univ p}
  have hfinite :=
    normalizedGradientRicciSoliton_finite_criticalPoints_of_compact_of_finrank_eq_two_of_not_constant
      (I := I) h hdim hnonconstant
  have hPcritical : P ⊆ criticalPoints I f := by
    intro p hp
    have hneg := mfderiv_eq_zero_at_spatial_min (I := I)
      ((hp.isLocalMax (by simp)).neg)
      ((f.contMDiff.neg p).mdifferentiableAt (by simp))
    have hnegfun : (fun x : M => -f x) = -(f : M → Real) := rfl
    rw [hnegfun, _root_.mfderiv_neg] at hneg
    exact neg_eq_zero.mp hneg
  have hPfinite : P.Finite := hfinite.subset hPcritical
  let _ : Fintype P := hPfinite.fintype
  obtain ⟨V, hV, hVdisj⟩ := hfinite.t2_separation
  obtain ⟨c, hc⟩ :=
    normalizedGradientRicciSoliton_exists_scalar_eq_const_mul_exp_of_finrank_eq_two
      (I := I) h hdim
  have hc0 : 0 ≤ c := by
    have hR := normalizedGradientRicciSoliton_scalar_nonneg (I := I) h xmin
    rw [hc xmin, mul_comm] at hR
    exact nonneg_of_mul_nonneg_right hR (Real.exp_pos _)
  let q : Real → Real := fun s => s - c * Real.exp s
  have hlocal : ∀ p : P, ∃ T : Real, T < f xmax ∧
      StrictAntiOn q (Set.Ici T) ∧
      ∃ e : OpenPartialHomeomorph M Plane,
        (p : M) ∈ e.source ∧ e p = 0 ∧
        (∀ x ∈ e.source, ‖e x‖ ^ 2 = normGradSqFun (I := I) g f x) ∧
        e.source ⊆ V p ∧ ∀ x ∈ e.source, T < f x := by
    intro p
    have hpmax : IsMaxOn f univ p := p.property
    have hfp : f p = f xmax :=
      le_antisymm (hmax (by simp)) (hpmax (by simp))
    have hscalarGt :=
      normalizedGradientRicciSoliton_one_lt_metricScalarAt_at_local_max_of_finrank_eq_two_of_not_constant
        (I := I) h hdim hnonconstant p (hpmax.isLocalMax (by simp))
    have hRGt := hscalarGt
    rw [hc p] at hRGt
    obtain ⟨T, hTp, hanti⟩ :=
      exists_lt_strictAntiOn_sub_const_mul_exp hc0 hRGt
    have hpcrit : IsCriticalPointAt I f p := hPcritical p.property
    have hcoef :
        (1 - metricScalarAt (I := I) (M := M) g p) / 2 ≠ 0 := by
      exact div_ne_zero (sub_ne_zero.mpr (ne_of_lt hscalarGt)) (by norm_num)
    obtain ⟨e0, hpe0, he0p, he0norm⟩ :=
      exists_openPartialHomeomorph_norm_sq_eq_normGradSqFun_of_hessFun_eq_smul_metric_of_finrank_eq_two
        (I := I) hdim g f p hpcrit hcoef
          (normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
            (I := I) h hdim p)
    let W : Set M := V p ∩ f ⁻¹' Set.Ioi T
    have hWopen : IsOpen W :=
      (hV p).2.inter (isOpen_Ioi.preimage f.contMDiff.continuous)
    let e : OpenPartialHomeomorph M Plane := e0.restrOpen W hWopen
    have hpe : (p : M) ∈ e.source := by
      change (p : M) ∈ e0.source ∩ W
      exact ⟨hpe0, (hV p).1, hTp⟩
    have hTmax : T < f xmax := by rw [← hfp]; exact hTp
    refine ⟨T, hTmax, hanti, e, hpe, ?_, ?_, ?_, ?_⟩
    · simpa only [e, OpenPartialHomeomorph.coe_restrOpen] using he0p
    · intro x hx
      apply he0norm x
      change x ∈ e0.source ∩ W at hx
      exact hx.1
    · intro x hx
      change x ∈ e0.source ∩ W at hx
      exact hx.2.1
    · intro x hx
      change x ∈ e0.source ∩ W at hx
      exact hx.2.2
  choose T hTmax hanti e hpe hep hnorm hsourceV hTf using hlocal
  have hlocalBall : ∀ p : P, ∃ R : Real, 0 < R ∧
      Metric.ball (0 : Plane) R ⊆ (e p).target := by
    intro p
    have hzeroTarget : (0 : Plane) ∈ (e p).target := by
      rw [← hep p]
      exact (e p).map_source (hpe p)
    exact Metric.mem_nhds_iff.mp ((e p).open_target.mem_nhds hzeroTarget)
  choose R hRpos hball using hlocalBall
  have hminmax : f xmin < f xmax := by
    have hle : f xmin ≤ f xmax := hmin (by simp)
    apply lt_of_le_of_ne hle
    intro heq
    apply hnonconstant
    intro y z
    apply le_antisymm
    · calc
        f y ≤ f xmax := hmax (by simp)
        _ = f xmin := heq.symm
        _ ≤ f z := hmin (by simp)
    · calc
        f z ≤ f xmax := hmax (by simp)
        _ = f xmin := heq.symm
        _ ≤ f y := hmin (by simp)
  have hqgrad : ∀ x : M,
      q (f x) = normGradSqFun (I := I) g f x := by
    intro x
    dsimp only [q]
    rw [← hc x]
    linarith [h.2.2 x]
  have hgradMax : gradFun (I := I) g f xmax = 0 :=
    gradientFun_eq_zero_of_isLocalMax (I := I) g
      (hmax.isLocalMax (by simp)) ((f.contMDiff xmax).mdifferentiableAt (by simp))
  have hqzero : q (f xmax) = 0 := by
    rw [hqgrad xmax]
    simp only [normGradSqFun_def, hgradMax, map_zero]
  let O : Set M := ⋃ p : P, (e p).source
  have hOopen : IsOpen O := isOpen_iUnion fun p => (e p).open_source
  let K : Set M := Oᶜ
  have hKcompact : IsCompact K := hOopen.isClosed_compl.isCompact
  have hfKcompact : IsCompact (f '' K) :=
    hKcompact.image f.contMDiff.continuous
  have hmaxNotImage : f xmax ∉ f '' K := by
    rintro ⟨x, hxK, hfx⟩
    have hxmax : IsMaxOn f univ x := by
      intro y hy
      rw [hfx]
      exact hmax hy
    let p : P := ⟨x, hxmax⟩
    have hxO : x ∈ O := Set.mem_iUnion.mpr ⟨p, hpe p⟩
    exact hxK hxO
  have havoid : (f '' K)ᶜ ∈ nhds (f xmax) :=
    hfKcompact.isClosed.isOpen_compl.mem_nhds hmaxNotImage
  have haboveMid : {s : Real | (f xmin + f xmax) / 2 < s} ∈ nhds (f xmax) :=
    isOpen_Ioi.mem_nhds (by
      change (f xmin + f xmax) / 2 < f xmax
      linarith [hminmax])
  have haboveT : ∀ p : P, {s : Real | T p < s} ∈ nhds (f xmax) := by
    intro p
    exact isOpen_Ioi.mem_nhds (hTmax p)
  have haboveTAll : ∀ᶠ s in nhds (f xmax), ∀ p : P, T p < s := by
    have hall :=
      (eventually_all_finset (Finset.univ : Finset P)).2
        (fun p _ => haboveT p)
    simpa only [Finset.mem_univ, forall_const] using hall
  have hqcontinuous : Continuous q :=
    continuous_id.sub (continuous_const.mul Real.continuous_exp)
  have hbelowRadius : ∀ p : P,
      {s : Real | q s < (R p) ^ 2} ∈ nhds (f xmax) := by
    intro p
    have hmem : Set.Iio ((R p) ^ 2) ∈ nhds (q (f xmax)) := by
      apply isOpen_Iio.mem_nhds
      change q (f xmax) < (R p) ^ 2
      rw [hqzero]
      exact sq_pos_of_pos (hRpos p)
    change q ⁻¹' Set.Iio ((R p) ^ 2) ∈ nhds (f xmax)
    exact hqcontinuous.continuousAt hmem
  have hbelowRadiusAll :
      ∀ᶠ s in nhds (f xmax), ∀ p : P, q s < (R p) ^ 2 := by
    have hall :=
      (eventually_all_finset (Finset.univ : Finset P)).2
        (fun p _ => hbelowRadius p)
    simpa only [Finset.mem_univ, forall_const] using hall
  have hgood : {s : Real |
      (f xmin + f xmax) / 2 < s ∧ (∀ p : P, T p < s) ∧
        (∀ p : P, q s < (R p) ^ 2) ∧ s ∉ f '' K} ∈ nhds (f xmax) := by
    filter_upwards [haboveMid, haboveTAll, hbelowRadiusAll, havoid] with s hsmid hsT hsR hsK
    exact ⟨hsmid, hsT, hsR, hsK⟩
  obtain ⟨l, u, hmaxIoo, hIoo⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hgood
  let b : Real := (l + f xmax) / 2
  have hbIoo : b ∈ Set.Ioo l u := by
    dsimp only [b]
    constructor <;> linarith [hmaxIoo.1, hmaxIoo.2]
  have hbGood := hIoo hbIoo
  have hbmax : b < f xmax := by
    dsimp only [b]
    linarith [hmaxIoo.1]
  have hqbpos : 0 < q b := by
    have hstrict := hanti (⟨xmax, hmax⟩ : P)
      (le_of_lt (hbGood.2.1 ⟨xmax, hmax⟩))
      (le_of_lt (hTmax ⟨xmax, hmax⟩)) hbmax
    rwa [hqzero] at hstrict
  have hlevelCover : f ⁻¹' {b} ⊆ O := by
    intro x hx
    by_contra hxO
    apply hbGood.2.2.2
    exact ⟨x, hxO, by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx⟩
  let r : Real := Real.sqrt (q b)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = q b := by
    exact Real.sq_sqrt (le_of_lt hqbpos)
  have hrR : ∀ p : P, r < R p := by
    intro p
    have hrnonneg : 0 ≤ r := Real.sqrt_nonneg _
    nlinarith [hbGood.2.2.1 p, hRpos p]
  let L : Set M := f ⁻¹' {b}
  let U : P → Set L := fun p => {x | (x : M) ∈ (e p).source}
  have hUopen : ∀ p : P, IsOpen (U p) := by
    intro p
    exact (e p).open_source.preimage continuous_subtype_val
  have hUdisj : Pairwise fun p z : P => Disjoint (U p) (U z) := by
    intro p z hpz
    rw [Set.disjoint_left]
    intro x hxp hxz
    have hpzM : (p : M) ≠ (z : M) := fun hpz' => hpz (Subtype.ext hpz')
    exact Set.disjoint_left.mp
      (hVdisj (hPcritical p.property) (hPcritical z.property) hpzM)
      (hsourceV p hxp) (hsourceV z hxz)
  have hUcover : ⋃ p : P, U p = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hxO : (x : M) ∈ O := hlevelCover x.property
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hxO
    exact Set.mem_iUnion.mpr ⟨p, hxp⟩
  have hUconn : ∀ p : P, IsConnected (U p) := by
    intro p
    apply isConnected_of_image_subtype_val
    have himage : Subtype.val '' U p =
        (e p).source ∩ (e p) ⁻¹' Metric.sphere (0 : Plane) r := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hlevel : f (y : M) = b := by
          simpa only [L, Set.mem_preimage, Set.mem_singleton_iff] using y.property
        have hnormsq : ‖e p y‖ ^ 2 = q b := by
          calc
            ‖e p y‖ ^ 2 = normGradSqFun (I := I) g f y := hnorm p y hy
            _ = q (f y) := (hqgrad y).symm
            _ = q b := by rw [hlevel]
        have hnormeq : ‖e p y‖ = r := by
          nlinarith [norm_nonneg (e p y), hr0]
        exact ⟨hy, by
          change dist (e p y) 0 = r
          simpa only [dist_zero_right] using hnormeq⟩
      · rintro ⟨hxsource, hxsphere⟩
        have hnormeq : ‖e p x‖ = r := by
          change dist (e p x) 0 = r at hxsphere
          simpa only [dist_zero_right] using hxsphere
        have hqeq : q (f x) = q b := by
          calc
            q (f x) = normGradSqFun (I := I) g f x := hqgrad x
            _ = ‖e p x‖ ^ 2 := (hnorm p x hxsource).symm
            _ = r ^ 2 := by rw [hnormeq]
            _ = q b := hrsq
        have hfx : f x = b := by
          apply (hanti p).injOn
          · exact le_of_lt (hTf p x hxsource)
          · exact le_of_lt (hbGood.2.1 p)
          · exact hqeq
        let y : L := ⟨x, by
          change f x ∈ ({b} : Set Real)
          simpa only [Set.mem_singleton_iff] using hfx⟩
        exact ⟨y, hxsource, rfl⟩
    rw [himage]
    exact isConnected_source_inter_preimage_sphere
      (e p) hr0 (hrR p) (hball p)
  let componentEquiv : ConnectedComponents L ≃ P :=
    connectedComponentsEquivOfPairwiseDisjointOpenConnectedCover
      U hUopen hUdisj hUcover hUconn
  refine ⟨b, hbGood.1, hbmax, ?_⟩
  change Nonempty (ConnectedComponents L ≃ P)
  exact ⟨componentEquiv⟩

private theorem normalizedGradientRicciSoliton_nonempty_equiv_minima_maxima_of_compact_of_finrank_eq_two_of_not_constant
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) :
    Nonempty ({p : M // IsMinOn f univ p} ≃
      {p : M // IsMaxOn f univ p}) := by
  obtain ⟨xmin, _, hmin⟩ :=
    (isCompact_univ : IsCompact (univ : Set M)).exists_isMinOn
      univ_nonempty f.contMDiff.continuous.continuousOn
  obtain ⟨xmax, _, hmax⟩ :=
    (isCompact_univ : IsCompact (univ : Set M)).exists_isMaxOn
      univ_nonempty f.contMDiff.continuous.continuousOn
  obtain ⟨a, hmina, hamid, ⟨emin⟩⟩ :=
    exists_low_regular_level_components_equiv_minima
      (I := I) h hdim hnonconstant hmin hmax
  obtain ⟨b, hmidb, hbmax, ⟨emax⟩⟩ :=
    exists_high_regular_level_components_equiv_maxima
      (I := I) h hdim hnonconstant hmin hmax
  have hab : a < b := lt_trans hamid hmidb
  have hcompact : IsCompact (f ⁻¹' Set.Icc a b) :=
    (isClosed_Icc.preimage f.contMDiff.continuous).isCompact
  have hregular : ∀ x ∈ f ⁻¹' Set.Icc a b,
      ¬ IsCriticalPointAt I f x := by
    intro x hx hxcrit
    have hextreme :=
      normalizedGradientRicciSoliton_isMinOn_or_isMaxOn_at_criticalPoint_of_compact_of_finrank_eq_two_of_not_constant
        (I := I) h hdim hnonconstant x hxcrit
    rcases hextreme with hxmin | hxmax
    · have hfx : f x = f xmin :=
        le_antisymm (hxmin (by simp)) (hmin (by simp))
      exact (not_lt_of_ge hx.1) (by simpa only [hfx] using hmina)
    · have hfx : f x = f xmax :=
        le_antisymm (hmax (by simp)) (hxmax (by simp))
      exact (not_lt_of_ge hx.2) (by simpa only [hfx] using hbmax)
  obtain ⟨v, _, hv, hsupp, hdfOn, hrate, _, _, _, _, _⟩ :=
    no_critical_value_transport (I := I) f f.contMDiff
      (le_of_lt hab) hcompact hregular
  let levelHome : (f ⁻¹' {a}) ≃ₜ (f ⁻¹' {b}) :=
    levelSetTransportHomeomorph I f f.contMDiff (le_of_lt hab)
      v hv hsupp hdfOn hrate
  have hfiber : ∀ y : f ⁻¹' {b},
      IsConnected (levelHome ⁻¹' {y}) := by
    intro y
    have heq : levelHome ⁻¹' {y} = {levelHome.symm y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff]
      exact levelHome.toEquiv.eq_symm_apply.symm
    rw [heq]
    exact isConnected_singleton
  let componentHome : ConnectedComponents (f ⁻¹' {a}) ≃ₜ
      ConnectedComponents (f ⁻¹' {b}) :=
    levelHome.isQuotientMap.isCoinducing.connectedComponentsHomeomorph hfiber
  exact ⟨emin.symm.trans (componentHome.toEquiv.trans emax)⟩

theorem normalizedGradientRicciSoliton_potential_constant_of_compact_of_finrank_eq_two
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2) :
    ∀ y z : M, f y = f z := by
  by_contra hnonconstant
  obtain ⟨xmin, xmax, hmin, hmax, hRmin, hRmax⟩ :=
    normalizedGradientRicciSoliton_exists_potential_extrema_with_scalar_lt_one_and_one_lt_of_compact_of_finrank_eq_two_of_not_constant
      (I := I) h hdim hnonconstant
  have hfinite :=
    normalizedGradientRicciSoliton_finite_criticalPoints_of_compact_of_finrank_eq_two_of_not_constant
      (I := I) h hdim hnonconstant
  let C := hfinite.toFinset
  let R : M → Real := fun x => metricScalarAt (I := I) (M := M) g x
  let P : ↥C → Prop := fun p => IsMinOn f univ (p : M)
  let Q : ↥C → Prop := fun p => IsMaxOn f univ (p : M)
  have hminCritical : ∀ p : M, IsMinOn f univ p → IsCriticalPointAt I f p := by
    intro p hp
    exact mfderiv_eq_zero_at_spatial_min (I := I)
      (hp.isLocalMin (by simp)) ((f.contMDiff p).mdifferentiableAt (by simp))
  have hmaxCritical : ∀ p : M, IsMaxOn f univ p → IsCriticalPointAt I f p := by
    intro p hp
    have hneg := mfderiv_eq_zero_at_spatial_min (I := I)
      ((hp.isLocalMax (by simp)).neg)
      ((f.contMDiff.neg p).mdifferentiableAt (by simp))
    have hnegfun : (fun x : M => -f x) = -(f : M → Real) := rfl
    rw [hnegfun, _root_.mfderiv_neg] at hneg
    exact neg_eq_zero.mp hneg
  obtain ⟨eminmax⟩ :=
    normalizedGradientRicciSoliton_nonempty_equiv_minima_maxima_of_compact_of_finrank_eq_two_of_not_constant
      (I := I) h hdim hnonconstant
  let emin : {p : ↥C // P p} ≃ {p : M // IsMinOn f univ p} :=
    { toFun := fun p => ⟨(p : M), p.property⟩
      invFun := fun p =>
        ⟨⟨p, hfinite.mem_toFinset.mpr (hminCritical p p.property)⟩, p.property⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  let emax : {p : ↥C // Q p} ≃ {p : M // IsMaxOn f univ p} :=
    { toFun := fun p => ⟨(p : M), p.property⟩
      invFun := fun p =>
        ⟨⟨p, hfinite.mem_toFinset.mpr (hmaxCritical p p.property)⟩, p.property⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  let e : {p : ↥C // P p} ≃ {p : ↥C // Q p} :=
    emin.trans (eminmax.trans emax.symm)
  have hcover : ∀ p : ↥C, P p ∨ Q p := by
    intro p
    exact
      normalizedGradientRicciSoliton_isMinOn_or_isMaxOn_at_criticalPoint_of_compact_of_finrank_eq_two_of_not_constant
        (I := I) h hdim hnonconstant p
          (hfinite.mem_toFinset.mp p.property)
  have hdisj : ∀ p : ↥C, ¬(P p ∧ Q p) := by
    intro p hp
    apply hnonconstant
    intro y z
    have hy : f y = f p := le_antisymm (hp.2 (by simp)) (hp.1 (by simp))
    have hz : f z = f p := le_antisymm (hp.2 (by simp)) (hp.1 (by simp))
    exact hy.trans hz.symm
  have hPnonempty : Nonempty {p : ↥C // P p} := by
    refine ⟨⟨⟨xmin, hfinite.mem_toFinset.mpr (hminCritical xmin hmin)⟩, hmin⟩⟩
  have hgradMin : gradFun (I := I) g f xmin = 0 :=
    gradientFun_eq_zero_of_isLocalMin (I := I) g
      (hmin.isLocalMin (by simp)) ((f.contMDiff xmin).mdifferentiableAt (by simp))
  have hgradMax : gradFun (I := I) g f xmax = 0 :=
    gradientFun_eq_zero_of_isLocalMax (I := I) g
      (hmax.isLocalMax (by simp)) ((f.contMDiff xmax).mdifferentiableAt (by simp))
  have hfmin : f xmin = R xmin :=
    normalizedGradientRicciSoliton_potential_eq_metricScalarAt_of_gradient_eq_zero
      (I := I) h xmin hgradMin
  have hfmax : f xmax = R xmax :=
    normalizedGradientRicciSoliton_potential_eq_metricScalarAt_of_gradient_eq_zero
      (I := I) h xmax hgradMax
  let F : ↥C → Real := fun p => 4 * Real.pi / (1 - R p)
  let A : Real := 4 * Real.pi / (1 - R xmin)
  let B : Real := 4 * Real.pi / (1 - R xmax)
  have hPA : ∀ p : ↥C, P p → F p = A := by
    intro p hp
    have hgradp : gradFun (I := I) g f p = 0 :=
      gradientFun_eq_zero_of_isLocalMin (I := I) g
        (hp.isLocalMin (by simp)) ((f.contMDiff p).mdifferentiableAt (by simp))
    have hfp : f p = R p :=
      normalizedGradientRicciSoliton_potential_eq_metricScalarAt_of_gradient_eq_zero
        (I := I) h p hgradp
    have hscalar : R p = R xmin := by
      calc
        R p = f p := hfp.symm
        _ = f xmin := le_antisymm (hp (by simp)) (hmin (by simp))
        _ = R xmin := hfmin
    simp only [F, A, hscalar]
  have hQB : ∀ p : ↥C, Q p → F p = B := by
    intro p hp
    have hgradp : gradFun (I := I) g f p = 0 :=
      gradientFun_eq_zero_of_isLocalMax (I := I) g
        (hp.isLocalMax (by simp)) ((f.contMDiff p).mdifferentiableAt (by simp))
    have hfp : f p = R p :=
      normalizedGradientRicciSoliton_potential_eq_metricScalarAt_of_gradient_eq_zero
        (I := I) h p hgradp
    have hscalar : R p = R xmax := by
      calc
        R p = f p := hfp.symm
        _ = f xmax := le_antisymm (hmax (by simp)) (hp (by simp))
        _ = R xmax := hfmax
    simp only [F, B, hscalar]
  have hsum : ∑ p : ↥C, F p = 0 := by
    simpa only [C, F, R] using
      sum_regularized_gradient_flux_at_criticalPoints_eq_zero
        (I := I) h hdim hnonconstant hfinite
  have hpair : A + B = 0 :=
    sum_eq_zero_partitioned_by_equicardinal_predicates
      P Q e hcover hdisj hPnonempty F A B hPA hQB hsum
  have hRminNe : 1 - R xmin ≠ 0 := sub_ne_zero.mpr (ne_of_gt hRmin)
  have hRmaxNe : 1 - R xmax ≠ 0 := sub_ne_zero.mpr (ne_of_lt hRmax)
  have hRsum : R xmin + R xmax = 2 := by
    dsimp only [A, B] at hpair
    field_simp [hRminNe, hRmaxNe, Real.pi_ne_zero] at hpair
    simp only [mul_zero] at hpair
    rcases mul_eq_zero.mp hpair with hpi | hlinear
    · exact False.elim ((mul_ne_zero (by norm_num) Real.pi_ne_zero) hpi)
    · linarith
  have hHamilton : R xmin * Real.exp (-R xmin) =
      R xmax * Real.exp (-R xmax) :=
    normalizedGradientRicciSoliton_metricScalarAt_mul_exp_neg_eq_of_finrank_eq_two_of_gradient_eq_zero
      (I := I) h hdim xmin xmax hgradMin hgradMax
  have hzero :
      (2 - R xmin) * Real.exp (R xmin - 2) -
        R xmin * Real.exp (-R xmin) = 0 := by
    have hRmaxEq : R xmax = 2 - R xmin := by linarith
    have hexpEq : R xmin - 2 = -R xmax := by linarith
    rw [← hRmaxEq, hexpEq]
    linarith
  have hstrict :=
    strictAntiOn_two_sub_mul_exp_sub_two_sub_mul_exp_neg_Iic_one
      (le_of_lt hRmin) (by simp) hRmin
  have hone :
      (2 - (1 : Real)) * Real.exp ((1 : Real) - 2) -
        (1 : Real) * Real.exp (-(1 : Real)) = 0 := by norm_num
  change
    (2 - (1 : Real)) * Real.exp ((1 : Real) - 2) -
        (1 : Real) * Real.exp (-(1 : Real)) <
      (2 - R xmin) * Real.exp (R xmin - 2) -
        R xmin * Real.exp (-R xmin) at hstrict
  rw [hone, hzero] at hstrict
  exact lt_irrefl 0 hstrict

end DifferentialGeometry.Geometry
