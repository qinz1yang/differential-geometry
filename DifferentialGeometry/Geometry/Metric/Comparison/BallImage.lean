import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Riemannian.Basic
import DifferentialGeometry.Topology.FirstExit

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PartialDiffeomorph

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
  intro y hy
  have hA : 0 < A := lt_of_le_of_lt dist_nonneg hy
  have hrR : r < R := by
    have hCA : 0 ≤ (C : ℝ) * A :=
      mul_nonneg C.property hA.le
    linarith
  have hxR : x ∈ Metric.ball O R := Metric.ball_subset_ball hrR.le hx
  have hballSrc : Metric.ball O R ⊆ Φ.source :=
    (Metric.ball_subset_closedBall.trans hsub)
  have hKcompact : IsCompact ((Φ : M → N) '' Metric.closedBall O R) :=
    hcompact.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hsub)
  have hKclosed : IsClosed ((Φ : M → N) '' Metric.closedBall O R) :=
    hKcompact.isClosed
  have hOpen : IsOpen ((Φ : M → N) '' Metric.ball O R) :=
    Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hballSrc
  have hOpenSub : (Φ : M → N) '' Metric.ball O R ⊆
      (Φ : M → N) '' Metric.closedBall O R :=
    Set.image_mono Metric.ball_subset_closedBall
  have hstart : (Φ : M → N) x ∈
      interior ((Φ : M → N) '' Metric.closedBall O R) := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (hOpen.mem_nhds ⟨x, hxR, rfl⟩) hOpenSub
  by_cases hyK : y ∈ (Φ : M → N) '' Metric.closedBall O R
  · exact hyK
  have hyEdist : Manifold.riemannianEDist J ((Φ : M → N) x) y <
      ENNReal.ofReal A := by
    rw [← IsRiemannianManifold.out (I := J), edist_dist,
      ENNReal.ofReal_lt_ofReal_iff hA]
    simpa only [Metric.mem_ball, dist_comm] using hy
  obtain ⟨η, hη0, hη1, hηC, hηlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt (I := J) hyEdist
  obtain ⟨t, ht, hstay, hfront⟩ :=
    exists_first_exit_frontier hKclosed zero_lt_one hηC.continuousOn (hη0 ▸ hstart) (hη1 ▸ hyK)
  have hηtK : η t ∈ (Φ : M → N) '' Metric.closedBall O R := by
    rw [← hKclosed.closure_eq]
    exact frontier_subset_closure hfront
  obtain ⟨x', hx'R, hx'eq⟩ := hηtK
  have hx'not : x' ∉ Metric.ball O R := by
    intro hx'ball
    have hInt' : (Φ : M → N) x' ∈
        interior ((Φ : M → N) '' Metric.closedBall O R) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (hOpen.mem_nhds ⟨x', hx'ball, rfl⟩) hOpenSub
    have hηtK' : η t ∈ (Φ : M → N) '' Metric.closedBall O R :=
      ⟨x', hx'R, hx'eq⟩
    exact (mem_frontier_iff_notMem_interior hηtK').mp hfront (hx'eq ▸ hInt')
  have hx'rad : dist O x' = R := by
    apply le_antisymm
    · simpa only [Metric.mem_closedBall, dist_comm] using hx'R
    · exact le_of_not_gt (fun hlt => hx'not (by
        simpa only [Metric.mem_ball, dist_comm] using hlt))
  let δ : Real → M := (Φ.symm : N → M) ∘ η
  have hδC : ContMDiffOn 𝓘(Real, Real) I 1 δ (Set.Icc 0 t) := by
    apply Φ.symm.contMDiffOn_toFun.comp
        (hηC.mono (Set.Icc_subset_Icc le_rfl ht.2))
    intro s hs
    obtain ⟨z, hzR, hzEq⟩ := hstay s hs
    change η s ∈ Φ.symm.source
    rw [← hzEq]
    exact Φ.map_source' (hsub hzR)
  have hxSrc : x ∈ Φ.source := hsub (Metric.ball_subset_closedBall hxR)
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
  have hxx' : dist x x' ≤ (C : ℝ) * A := by
    have hedLe : Manifold.riemannianEDist I x x' ≤
        ENNReal.ofReal ((C : ℝ) * A) :=
      (Manifold.riemannianEDist_le_pathELength hδC hδ0 hδt ht.1.le).trans hδle
    rw [← IsRiemannianManifold.out (I := I), edist_dist] at hedLe
    exact ENNReal.ofReal_le_ofReal_iff (mul_nonneg C.property hA.le) |>.mp hedLe
  have hxDist : dist O x < r := by
    simpa only [Metric.mem_ball, dist_comm] using hx
  have hcontra : dist O x' < R := by
    calc
      dist O x' ≤ dist O x + dist x x' := dist_triangle _ _ _
      _ < r + (C : ℝ) * A := add_lt_add_of_lt_of_le hxDist hxx'
      _ = (C : ℝ) * A + r := add_comm _ _
      _ < R := hmargin
  linarith

end DifferentialGeometry.PartialDiffeomorph
