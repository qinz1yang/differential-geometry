import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Riemannian.Basic
import DifferentialGeometry.Topology.FirstExit

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PartialDiffeomorph

theorem eball_subset_image_closedEBall_of_enorm_mfderiv_symm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
    {N : Type*} [PseudoEMetricSpace N] [ChartedSpace G N] [T2Space N]
    [RiemannianBundle (fun x : N => TangentSpace J x)] [IsRiemannianManifold J N]
    (Φ : PartialDiffeomorph I J M N 1) {O x : M} {r R A : ℝ} {C : NNReal}
    (hcompact : IsCompact (Metric.closedEBall O (ENNReal.ofReal R)))
    (hsub : Metric.closedEBall O (ENNReal.ofReal R) ⊆ Φ.source)
    (hspeed : ∀ z ∈ (Φ : M → N) '' Metric.closedEBall O (ENNReal.ofReal R),
      ∀ w : TangentSpace J z, ‖mfderiv J I (Φ.symm : N → M) z w‖ₑ ≤
        ENNReal.ofReal (C : ℝ) * ‖w‖ₑ)
    (hx : x ∈ Metric.eball O (ENNReal.ofReal r)) (hmargin : (C : ℝ) * A + r < R) :
    Metric.eball ((Φ : M → N) x) (ENNReal.ofReal A) ⊆
      (Φ : M → N) '' Metric.closedEBall O (ENNReal.ofReal R) := by
  intro y hy
  have hA : 0 < A := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hy)
  have hrR : r < R := by
    have hCA : 0 ≤ (C : ℝ) * A :=
      mul_nonneg C.property hA.le
    linarith
  have hxR : x ∈ Metric.eball O (ENNReal.ofReal R) :=
    Metric.eball_subset_eball (ENNReal.ofReal_le_ofReal hrR.le) hx
  have hballSrc : Metric.eball O (ENNReal.ofReal R) ⊆ Φ.source :=
    (Metric.eball_subset_closedEBall.trans hsub)
  have hKcompact : IsCompact ((Φ : M → N) '' Metric.closedEBall O (ENNReal.ofReal R)) :=
    hcompact.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hsub)
  have hKclosed : IsClosed ((Φ : M → N) '' Metric.closedEBall O (ENNReal.ofReal R)) :=
    hKcompact.isClosed
  have hOpen : IsOpen ((Φ : M → N) '' Metric.eball O (ENNReal.ofReal R)) :=
    Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_eball hballSrc
  have hOpenSub : (Φ : M → N) '' Metric.eball O (ENNReal.ofReal R) ⊆
      (Φ : M → N) '' Metric.closedEBall O (ENNReal.ofReal R) :=
    Set.image_mono Metric.eball_subset_closedEBall
  have hstart : (Φ : M → N) x ∈
      interior ((Φ : M → N) '' Metric.closedEBall O (ENNReal.ofReal R)) := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (hOpen.mem_nhds ⟨x, hxR, rfl⟩) hOpenSub
  by_cases hyK : y ∈ (Φ : M → N) '' Metric.closedEBall O (ENNReal.ofReal R)
  · exact hyK
  have hyEdist : Manifold.riemannianEDist J ((Φ : M → N) x) y <
      ENNReal.ofReal A := by
    rw [← IsRiemannianManifold.out (I := J)]
    simpa only [Metric.mem_eball, edist_comm] using hy
  obtain ⟨η, hη0, hη1, hηC, hηlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt (I := J) hyEdist
  obtain ⟨t, ht, hstay, hfront⟩ :=
    exists_first_exit_frontier hKclosed zero_lt_one hηC.continuousOn (hη0 ▸ hstart) (hη1 ▸ hyK)
  have hηtK : η t ∈ (Φ : M → N) '' Metric.closedEBall O (ENNReal.ofReal R) := by
    rw [← hKclosed.closure_eq]
    exact frontier_subset_closure hfront
  obtain ⟨x', hx'R, hx'eq⟩ := hηtK
  have hx'not : x' ∉ Metric.eball O (ENNReal.ofReal R) := by
    intro hx'ball
    have hInt' : (Φ : M → N) x' ∈
        interior ((Φ : M → N) '' Metric.closedEBall O (ENNReal.ofReal R)) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (hOpen.mem_nhds ⟨x', hx'ball, rfl⟩) hOpenSub
    have hηtK' : η t ∈ (Φ : M → N) '' Metric.closedEBall O (ENNReal.ofReal R) :=
      ⟨x', hx'R, hx'eq⟩
    exact (mem_frontier_iff_notMem_interior hηtK').mp hfront (hx'eq ▸ hInt')
  have hx'rad : ENNReal.ofReal R ≤ edist O x' := by
    exact le_of_not_gt (fun hlt => hx'not (by
      simpa only [Metric.mem_eball, edist_comm] using hlt))
  let δ : Real → M := (Φ.symm : N → M) ∘ η
  have hδC : ContMDiffOn 𝓘(Real, Real) I 1 δ (Set.Icc 0 t) := by
    apply Φ.symm.contMDiffOn_toFun.comp
        (hηC.mono (Set.Icc_subset_Icc le_rfl ht.2))
    intro s hs
    obtain ⟨z, hzR, hzEq⟩ := hstay s hs
    change η s ∈ Φ.symm.source
    rw [← hzEq]
    exact Φ.map_source' (hsub hzR)
  have hxSrc : x ∈ Φ.source := hsub (Metric.eball_subset_closedEBall hxR)
  have hx'Src : x' ∈ Φ.source := hsub hx'R
  have hδ0 : δ 0 = x := by
    simp only [δ, Function.comp_apply, hη0]
    exact Φ.left_inv hxSrc
  have hδt : δ t = x' := by
    change (Φ.symm : N → M) (η t) = x'
    rw [← hx'eq]
    exact Φ.left_inv hx'Src
  have hlen : Manifold.pathELength (I := I) δ 0 t ≤
      ENNReal.ofReal (C : ℝ) *
        Manifold.pathELength (I := J) η 0 t := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
      Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
      ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_mono_ae
      (Filter.eventually_of_mem
        (MeasureTheory.self_mem_ae_restrict measurableSet_Ioo) ?_)
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : Real) t := Set.mem_Icc_of_Ioo hs
    have hηsK := hstay s hsIcc
    obtain ⟨z, hzR, hzEq⟩ := hηsK
    have hηd : MDifferentiableAt 𝓘(Real, Real) J η s := by
      refine ((hηC.contMDiffAt ?_).mdifferentiableAt (by norm_num))
      exact Icc_mem_nhds hs.1 (hs.2.trans_le ht.2)
    have hΦd : MDifferentiableAt J I (Φ.symm : N → M) (η s) := by
      rw [← hzEq]
      exact (Φ.symm.contMDiffOn_toFun.contMDiffAt
        (Φ.symm.open_source.mem_nhds (Φ.map_source' (hsub hzR)))).mdifferentiableAt one_ne_zero
    have happ : mfderiv 𝓘(Real, Real) I δ s 1 =
        mfderiv J I (Φ.symm : N → M) (η s)
          (mfderiv 𝓘(Real, Real) J η s 1) :=
      mfderiv_comp_apply s hΦd hηd 1
    rw [happ]
    set w := mfderiv 𝓘(Real, Real) J η s 1
    exact hspeed (η s) ⟨z, hzR, hzEq⟩ w
  have hlenPrefix : Manifold.pathELength (I := J) η 0 t ≤
      Manifold.pathELength (I := J) η 0 1 :=
    Manifold.pathELength_mono le_rfl ht.2
  have hδle : Manifold.pathELength (I := I) δ 0 t ≤
      ENNReal.ofReal ((C : ℝ) * A) := by
    calc
      Manifold.pathELength (I := I) δ 0 t ≤
          ENNReal.ofReal (C : ℝ) * Manifold.pathELength (I := J) η 0 t := hlen
      _ ≤ ENNReal.ofReal (C : ℝ) * Manifold.pathELength (I := J) η 0 1 :=
        by gcongr
      _ ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal A :=
        by gcongr
      _ = ENNReal.ofReal ((C : ℝ) * A) := (ENNReal.ofReal_mul C.property).symm
  have hxx' : edist x x' ≤ ENNReal.ofReal ((C : ℝ) * A) := by
    have hedLe : Manifold.riemannianEDist I x x' ≤
        ENNReal.ofReal ((C : ℝ) * A) :=
      (Manifold.riemannianEDist_le_pathELength hδC hδ0 hδt ht.1.le).trans hδle
    rwa [← IsRiemannianManifold.out (I := I)] at hedLe
  have hxDist : edist O x < ENNReal.ofReal r := by
    simpa only [Metric.mem_eball, edist_comm] using hx
  have hr : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hxDist)
  have hcontra : edist O x' < ENNReal.ofReal R := by
    calc
      edist O x' ≤ edist O x + edist x x' := edist_triangle _ _ _
      _ < ENNReal.ofReal r + ENNReal.ofReal ((C : ℝ) * A) :=
        ENNReal.add_lt_add_of_lt_of_le
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxx') hxDist hxx'
      _ = ENNReal.ofReal (r + (C : ℝ) * A) :=
        (ENNReal.ofReal_add hr.le (mul_nonneg C.property hA.le)).symm
      _ < ENNReal.ofReal R :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < R)).mpr (by linarith)
  exact ((not_lt_of_ge hx'rad) hcontra).elim

theorem ball_subset_image_closedBall_of_enorm_mfderiv_symm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
    {N : Type*} [PseudoMetricSpace N] [ChartedSpace G N] [T2Space N]
    [RiemannianBundle (fun x : N => TangentSpace J x)] [IsRiemannianManifold J N]
    (Φ : PartialDiffeomorph I J M N 1) {O x : M} {r R A : ℝ} {C : NNReal}
    (hcompact : IsCompact (Metric.closedBall O R))
    (hsub : Metric.closedBall O R ⊆ Φ.source)
    (hspeed : ∀ z ∈ (Φ : M → N) '' Metric.closedBall O R,
      ∀ w : TangentSpace J z, ‖mfderiv J I (Φ.symm : N → M) z w‖ₑ ≤
        ENNReal.ofReal (C : ℝ) * ‖w‖ₑ)
    (hx : x ∈ Metric.ball O r) (hmargin : (C : ℝ) * A + r < R) :
    Metric.ball ((Φ : M → N) x) A ⊆ (Φ : M → N) '' Metric.closedBall O R := by
  by_cases hA : 0 < A
  · have hr : 0 < r := lt_of_le_of_lt dist_nonneg hx
    have hCA : 0 ≤ (C : ℝ) * A := mul_nonneg C.property hA.le
    have hR : 0 < R := by linarith
    have hc : IsCompact (Metric.closedEBall O (ENNReal.ofReal R)) := by
      simpa only [Metric.closedEBall_ofReal hR.le] using hcompact
    have hs : Metric.closedEBall O (ENNReal.ofReal R) ⊆ Φ.source := by
      simpa only [Metric.closedEBall_ofReal hR.le] using hsub
    have hv : ∀ z ∈ (Φ : M → N) '' Metric.closedEBall O (ENNReal.ofReal R),
        ∀ w : TangentSpace J z, ‖mfderiv J I (Φ.symm : N → M) z w‖ₑ ≤
          ENNReal.ofReal (C : ℝ) * ‖w‖ₑ := by
      simpa only [Metric.closedEBall_ofReal hR.le] using hspeed
    have hx' : x ∈ Metric.eball O (ENNReal.ofReal r) := by
      simpa only [Metric.eball_ofReal] using hx
    simpa only [Metric.eball_ofReal, Metric.closedEBall_ofReal hR.le] using
      eball_subset_image_closedEBall_of_enorm_mfderiv_symm_le Φ hc hs hv hx' hmargin
  · rw [Metric.ball_eq_empty.mpr (le_of_not_gt hA)]
    exact empty_subset _

end DifferentialGeometry.PartialDiffeomorph
