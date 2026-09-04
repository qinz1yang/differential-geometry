import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.Isometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Transport
import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.FiberRegion
import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Filter
open DifferentialGeometry.Analysis.InnerProductSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators
open scoped Matrix.Norms.Frobenius

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
variable [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
private theorem pulledRm_normSq_eq_rm_normSq
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) :
    normSq0S (I := I) (S.base.metric 0) x 4 (uhlenbeckPulledRm04At S basisAt iota t x) =
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) := by
  have hinner := fiberInner_compUhlenbeck_isometry (I := I) (M := M) hT S basisAt iota hiota0
    hgram horth0 ht x
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) x⟩
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) x⟩
  unfold normSq0S
  exact hinner

omit [SigmaCompactSpace M] in
private theorem pulledRm_norm_eq_rm_norm
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) :
    tensor04FiberNorm (S.base.metric 0) x (uhlenbeckPulledRm04At S basisAt iota t x) =
      tensor04FiberNorm (S.base.metric t) x (S.base.rm04 t x) := by
  unfold tensor04FiberNorm tensor0SFiberNorm
  rw [pulledRm_normSq_eq_rm_normSq (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht x]

variable [NeZero (Module.finrank ℝ E)]

open DifferentialGeometry.Integral.Measure

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
private theorem chartFrameNorm_continuousOn_ricciFlow
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
          (chartFrameNorm (I := I) (S.base.metric q.1) α i q.2))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) := by
  have hG : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Set.Icc 0 T)
      (fun t x => metricTensorField (I := I) (S.base.metric t) x) := by
    have hmono : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Set.Icc 0 T)
        (fun t x => metricTensorField (I := I) (S.family.metric t) x) :=
      tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
        hS.smoothMetric.metricTensor_cont (by intro s hs; exact hs)
    refine tensor0SFamilyContinuousOnSet.congr (I := I) (M := M) hmono ?_
    intro t ht x
    rfl
  exact chartFrameNorm_continuousOn_metricFamily (I := I) (M := M)
    S.base.metric hG α i

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)] in
private theorem normSq0S_eq_four_mul_matrixNormSq_of_frame
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3)
    (e : Fin 3 → TangentSpace I x)
    (horth : ∀ i j : Fin 3, g.inner x (e i) (e j) = if i = j then 1 else 0)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    normSq0S (I := I) g x 4 (A : Tensor04At (I := I) (M := M) x) =
      4 * ‖matrixToEuclidean (fun i j : Fin 3 =>
        tensor04StandardAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (e (bivectorIndex3 i).1) (e (bivectorIndex3 i).2)
          (e (bivectorIndex3 j).2) (e (bivectorIndex3 j).1))‖ ^ 2 := by
  classical
  have hli : LinearIndependent ℝ e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hpair : g.inner x (∑ j, c j • e j) (e i) = 0 := by
      rw [hc]; simp
    rw [map_sum, sum_apply] at hpair
    rw [Finset.sum_eq_single i] at hpair
    · rw [ContinuousLinearMap.map_smul, smul_apply,
        horth i i, if_pos rfl, smul_eq_mul, mul_one] at hpair
      exact hpair
    · intro j _ hji
      rw [ContinuousLinearMap.map_smul, smul_apply,
        horth j i, if_neg (by simpa using hji), smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin, hdim]
  have hsp : Submodule.span ℝ (Set.range e) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank hcard
  let basis : Module.Basis (Fin 3) ℝ (TangentSpace I x) :=
    Module.Basis.mk hli hsp.symm.le
  have hbasis_eq : (basis : Fin 3 → TangentSpace I x) = e := by
    funext i
    exact Module.Basis.mk_apply hli hsp.symm.le i
  have horthB : OrthonormalBasisAt (I := I) g x basis := by
    intro i j
    rw [hbasis_eq]
    exact horth i j
  have hmain := inner0S_algebraic_eq_four_mul_matrixInner (I := I) (M := M) g x basis horthB A A
  have hmat : tensor04CurvatureOperatorMatrixAt (I := I) basis
        (A : Tensor04At (I := I) (M := M) x) =
      fun i j : Fin 3 =>
      tensor04StandardAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
        (e (bivectorIndex3 i).1) (e (bivectorIndex3 i).2)
        (e (bivectorIndex3 j).2) (e (bivectorIndex3 j).1) := by
    ext i j
    simp [hbasis_eq]
  rw [normSq0S]
  rw [hmain]
  rw [hmat]
  rw [show inner ℝ (matrixToEuclidean (fun i j : Fin 3 =>
        tensor04StandardAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (e (bivectorIndex3 i).1) (e (bivectorIndex3 i).2)
          (e (bivectorIndex3 j).2) (e (bivectorIndex3 j).1)))
      (matrixToEuclidean (fun i j : Fin 3 =>
        tensor04StandardAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (e (bivectorIndex3 i).1) (e (bivectorIndex3 i).2)
          (e (bivectorIndex3 j).2) (e (bivectorIndex3 j).1))) =
      ‖matrixToEuclidean (fun i j : Fin 3 =>
        tensor04StandardAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (e (bivectorIndex3 i).1) (e (bivectorIndex3 i).2)
          (e (bivectorIndex3 j).2) (e (bivectorIndex3 j).1))‖ ^ 2 by
    rw [norm_sq_eq_re_inner (𝕜 := ℝ) (matrixToEuclidean (fun i j : Fin 3 =>
        tensor04StandardAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (e (bivectorIndex3 i).1) (e (bivectorIndex3 i).2)
          (e (bivectorIndex3 j).2) (e (bivectorIndex3 j).1)))]
    simp]

omit [SigmaCompactSpace M] in
private lemma normSq0S_rm04_continuousOn_local
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (α : M) :
    ContinuousOn (fun q : ℝ × M =>
        normSq0S (I := I) (S.base.metric q.1) q.2 4 (S.base.rm04 q.1 q.2))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) := by
  classical
  let U : Set M := smoothOrthoOpen (I := I) (M := M) α
  have hU_base : ∀ q : ℝ × M,
      q ∈ Set.Icc 0 T ×ˢ U →
      q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro q hq
    exact smoothOrthoOpen_subset_baseSet (I := I) (M := M) α hq.2
  have hfe (x : M) : Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I x) := by
    have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H x
    exact ((trivializationAt E (TangentSpace I) x).linearEquivAt ℝ x hx).finrank_eq.symm
  let idx (x : M) (a : Fin 3) : Fin (Module.finrank ℝ E) :=
    ⟨a.val, by rw [hfe x, hdim x]; exact a.isLt⟩
  let e (a : Fin 3) (q : ℝ × M) : TangentSpace I q.2 :=
    chartFrameNorm (I := I) (S.base.metric q.1) α (idx q.2 a) q.2
  have he_cont : ∀ a : Fin 3,
      ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2 (e a q))
        (Set.Icc 0 T ×ˢ U) := by
    intro a
    have hmain := chartFrameNorm_continuousOn_ricciFlow (I := I) (M := M) hT S hS α (idx α a)
    refine hmain.congr ?_
    intro q hq
    change TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2
        (chartFrameNorm (I := I) (S.base.metric q.1) α (idx q.2 a) q.2) =
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2
        (chartFrameNorm (I := I) (S.base.metric q.1) α (idx α a) q.2)
    apply congrArg (fun i : Fin (Module.finrank ℝ E) =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2
        (chartFrameNorm (I := I) (S.base.metric q.1) α i q.2))
    apply Fin.ext
    rfl
  have he_orth : ∀ a b : Fin 3, ∀ q : ℝ × M,
      q ∈ Set.Icc 0 T ×ˢ U →
      (S.base.metric q.1).inner q.2 (e a q) (e b q) = if a = b then 1 else 0 := by
    intro a b q hq
    have horth := chartFrameNorm_orthonormal (I := I) (S.base.metric q.1) α
      (hU_base q hq) (idx q.2 a) (idx q.2 b)
    have hidx : idx q.2 a = idx q.2 b ↔ a = b := by
      constructor
      · intro h
        apply Fin.ext
        simpa using (congrArg (fun i : Fin (Module.finrank ℝ E) => i.val) h)
      · intro h
        rw [h]
    change (S.base.metric q.1).inner q.2
        (chartFrameNorm (I := I) (S.base.metric q.1) α (idx q.2 a) q.2)
        (chartFrameNorm (I := I) (S.base.metric q.1) α (idx q.2 b) q.2) =
      if a = b then 1 else 0
    rw [horth]
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (by rw [hab])]
    · rw [if_neg hab, if_neg (fun h => hab (hidx.mp h))]
  have hentry4 : ∀ a b c d : Fin 3,
      ContinuousOn (fun q : ℝ × M =>
        tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e a q) (e b q) (e c q) (e d q))
        (Set.Icc 0 T ×ˢ U) := by
    intro a b c d
    have hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 (Set.Icc 0 T)
        (fun t x => S.base.rm04 t x) := by
      exact tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
        hS.rm04Cont (by intro s hs; exact hs)
    rw [continuousOn_iff_continuous_domRestrict]
    let P := {q : ℝ × M // q ∈ Set.Icc 0 T ×ˢ U}
    have heval := tensor0SFamilyContinuousOnSet.eval_continuous (I := I) (M := M) (s := 4)
      (K := Set.Icc 0 T) (A := fun t x => S.base.rm04 t x) hA
      (P := P) (τ := fun p : P => p.1.1) (b := fun p : P => p.1.2)
      (continuous_fst.comp continuous_subtype_val) (fun p : P => p.2.1)
      (continuous_snd.comp continuous_subtype_val)
      (v := fun i : Fin 4 => fun p : P =>
        if i = 0 then e a p.1 else if i = 1 then e b p.1 else if i = 2 then e c p.1 else e d p.1)
      (by
        intro i
        fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
          change Continuous ((Set.Icc 0 T ×ˢ U).domRestrict fun q : ℝ × M =>
            TotalSpace.mk' E q.2 (e a q))
          exact continuousOn_iff_continuous_domRestrict.mp (he_cont a)
        · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
          change Continuous ((Set.Icc 0 T ×ˢ U).domRestrict fun q : ℝ × M =>
            TotalSpace.mk' E q.2 (e b q))
          exact continuousOn_iff_continuous_domRestrict.mp (he_cont b)
        · simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          change Continuous ((Set.Icc 0 T ×ˢ U).domRestrict fun q : ℝ × M =>
            TotalSpace.mk' E q.2 (e c q))
          exact continuousOn_iff_continuous_domRestrict.mp (he_cont c)
        · simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          change Continuous ((Set.Icc 0 T ×ˢ U).domRestrict fun q : ℝ × M =>
            TotalSpace.mk' E q.2 (e d q))
          exact continuousOn_iff_continuous_domRestrict.mp (he_cont d))
    refine heval.congr (fun p => ?_)
    change (S.base.rm04 p.1.1 p.1.2)
        (fun i : Fin 4 => if i = 0 then e a p.1 else if i = 1 then e b p.1 else if i = 2 then e c p.1 else e d p.1) =
      tensor04StandardAt (I := I) (M := M) (S.base.rm04 p.1.1 p.1.2)
        (e a p.1) (e b p.1) (e c p.1) (e d p.1)
    rw [tensor04StandardAt]
    congr 1
  have hentry : ∀ a b : Fin 3,
      ContinuousOn (fun q : ℝ × M =>
        tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 a).1 q) (e (bivectorIndex3 a).2 q)
          (e (bivectorIndex3 b).2 q) (e (bivectorIndex3 b).1 q))
        (Set.Icc 0 T ×ˢ U) := by
    intro a b
    exact hentry4 (bivectorIndex3 a).1 (bivectorIndex3 a).2 (bivectorIndex3 b).2 (bivectorIndex3 b).1
  have hsum_cont : ContinuousOn (fun q : ℝ × M =>
      4 * (∑ a : Fin 3, ∑ b : Fin 3,
        (tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 a).1 q) (e (bivectorIndex3 a).2 q)
          (e (bivectorIndex3 b).2 q) (e (bivectorIndex3 b).1 q)) ^ 2))
      (Set.Icc 0 T ×ˢ U) := by
    have hsum : ContinuousOn (fun q : ℝ × M =>
        ∑ a : Fin 3, ∑ b : Fin 3,
          (tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
            (e (bivectorIndex3 a).1 q) (e (bivectorIndex3 a).2 q)
            (e (bivectorIndex3 b).2 q) (e (bivectorIndex3 b).1 q)) ^ 2)
        (Set.Icc 0 T ×ˢ U) := by
      refine continuousOn_finsetSum Finset.univ ?_
      intro a _
      refine continuousOn_finsetSum Finset.univ ?_
      intro b _
      exact (hentry a b).pow 2
    exact (continuousOn_const.mul hsum)
  refine hsum_cont.congr ?_
  intro q hq
  change normSq0S (I := I) (S.base.metric q.1) q.2 4
      ((⟨S.base.rm04 q.1 q.2, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric q.1) q.2⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) q.2) :
        Tensor04At (I := I) (M := M) q.2) =
    4 * (∑ a : Fin 3, ∑ b : Fin 3,
        (tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 a).1 q) (e (bivectorIndex3 a).2 q)
          (e (bivectorIndex3 b).2 q) (e (bivectorIndex3 b).1 q)) ^ 2)
  have hframe := normSq0S_eq_four_mul_matrixNormSq_of_frame (I := I) (M := M)
    (S.base.metric q.1) q.2 (hdim q.2) (fun a => e a q)
    (by intro a b; exact he_orth a b q hq)
    ⟨S.base.rm04 q.1 q.2, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric q.1) q.2⟩
  have hnorm : ‖matrixToEuclidean (fun i j : Fin 3 =>
        tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
          (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q))‖ ^ 2 =
      ∑ a : Fin 3, ∑ b : Fin 3,
        (tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 a).1 q) (e (bivectorIndex3 a).2 q)
          (e (bivectorIndex3 b).2 q) (e (bivectorIndex3 b).1 q)) ^ 2 := by
    have hsum := inner_matrixToEuclidean
      (matrixToEuclidean (fun i j : Fin 3 =>
        tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
          (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q)))
      (fun i j : Fin 3 => tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
        (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
        (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q))
    calc
      ‖matrixToEuclidean (fun i j : Fin 3 =>
          tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
            (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
            (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q))‖ ^ 2
          = inner ℝ (matrixToEuclidean (fun i j : Fin 3 =>
              tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
                (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
                (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q)))
              (matrixToEuclidean (fun i j : Fin 3 =>
              tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
                (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
                (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q))) := by
            rw [norm_sq_eq_re_inner (𝕜 := ℝ) (matrixToEuclidean (fun i j : Fin 3 =>
              tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
                (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
                (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q)))]
            simp
      _ = ∑ a : Fin 3, ∑ b : Fin 3,
            (tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
              (e (bivectorIndex3 a).1 q) (e (bivectorIndex3 a).2 q)
              (e (bivectorIndex3 b).2 q) (e (bivectorIndex3 b).1 q)) ^ 2 := by
            rw [hsum, Fintype.sum_prod_type]
            simp [matrixToEuclidean, pow_two]
  rw [hframe]
  rw [hnorm]

omit [SigmaCompactSpace M] in
private theorem tensor04FiberNorm_rm04_continuousOn
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3) :
    ContinuousOn (fun q : ℝ × M =>
        tensor04FiberNorm (S.base.metric q.1) q.2 (S.base.rm04 q.1 q.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
  classical
  intro q hq
  let α : M := q.2
  have hlocal := normSq0S_rm04_continuousOn_local (I := I) (M := M) hT S hS hdim α
  have hsq : ContinuousOn (fun r : ℝ × M =>
      Real.sqrt (normSq0S (I := I) (S.base.metric r.1) r.2 4 (S.base.rm04 r.1 r.2)))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) := hlocal.sqrt
  have hqL : q ∈ Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α := by
    exact ⟨hq.1, mem_smoothOrthoOpen (I := I) (M := M) α⟩
  have hL : ContinuousWithinAt
      (fun r : ℝ × M => Real.sqrt (normSq0S (I := I) (S.base.metric r.1) r.2 4 (S.base.rm04 r.1 r.2)))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) q :=
    hsq.continuousWithinAt hqL
  have hmem_nhds : (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) ∈
      𝓝[(Set.Icc 0 T ×ˢ (Set.univ : Set M))] q := by
    rw [mem_nhdsWithin]
    refine ⟨Set.univ ×ˢ smoothOrthoOpen (I := I) (M := M) α, ?_, ?_, ?_⟩
    · exact isOpen_univ.prod (smoothOrthoOpen_open (I := I) (M := M) α)
    · exact ⟨trivial, mem_smoothOrthoOpen (I := I) (M := M) α⟩
    · intro r hr
      have hEq : (Set.univ ×ˢ smoothOrthoOpen (I := I) (M := M) α) ∩
          (Set.Icc 0 T ×ˢ (Set.univ : Set M)) =
          Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α := by
        rw [Set.prod_inter_prod]
        simp
      exact (hEq ▸ hr)
  have heq : 𝓝[(Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α)] q =
      𝓝[(Set.Icc 0 T ×ˢ (Set.univ : Set M))] q := by
    apply le_antisymm
    · exact nhdsWithin_mono q (by
        intro r hr
        exact Set.mem_prod.mpr ⟨(Set.mem_prod.mp hr).1, trivial⟩)
    · exact (nhdsWithin_le_iff (s := (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
        (t := (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α)) (x := q)).mpr hmem_nhds
  have hT' : ContinuousWithinAt
      (fun r : ℝ × M => Real.sqrt (normSq0S (I := I) (S.base.metric r.1) r.2 4 (S.base.rm04 r.1 r.2)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) q := by
    change Tendsto (fun r : ℝ × M =>
        Real.sqrt (normSq0S (I := I) (S.base.metric r.1) r.2 4 (S.base.rm04 r.1 r.2)))
      (𝓝[(Set.Icc 0 T ×ˢ (Set.univ : Set M))] q)
      (𝓝 (Real.sqrt (normSq0S (I := I) (S.base.metric q.1) q.2 4 (S.base.rm04 q.1 q.2))))
    rw [← heq]
    exact hL
  change ContinuousWithinAt
    (fun r : ℝ × M => Real.sqrt
      (normSq0S (I := I) (S.base.metric r.1) r.2 4 (S.base.rm04 r.1 r.2)))
    (Set.Icc 0 T ×ˢ (Set.univ : Set M)) q
  exact hT'


omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
theorem exists_pulledRm_norm_bound
    {T : ℝ} (hT : 0 < T) [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M,
      letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
        (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
      letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
        @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
      letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
        @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
      ‖uhlenbeckPulledRm04At S basisAt iota t x‖ ≤ R := by
  classical
  let s : Set (ℝ × M) := Set.Icc 0 T ×ˢ (Set.univ : Set M)
  let f : ℝ × M → ℝ := fun q =>
    tensor04FiberNorm (S.base.metric q.1) q.2 (S.base.rm04 q.1 q.2)
  have hf_cont : ContinuousOn f s := by
    simpa [f, s] using tensor04FiberNorm_rm04_continuousOn (I := I) (M := M) hT S hS hdim
  have hs_compact : IsCompact s := by
    dsimp [s]
    exact isCompact_Icc.prod (CompactSpace.isCompact_univ : IsCompact (Set.univ : Set M))
  rcases (hs_compact.bddAbove_image hf_cont) with ⟨R, hR⟩
  let R' : ℝ := max R 0
  refine ⟨R', ?_, ?_⟩
  · dsimp [R']
    exact le_max_right _ _
  · intro t ht x
    have hx : (t, x) ∈ s := by simp [s, ht]
    have hle : f (t, x) ≤ R := hR (Set.mem_image_of_mem f hx)
    let : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
      (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
    let : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
        inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
    let : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
      @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
        inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
    have heq : ‖uhlenbeckPulledRm04At S basisAt iota t x‖ = f (t, x) := by
      have h1 := tensor0SFiberNorm_eq_norm (I := I) (S.base.metric 0) x
        (uhlenbeckPulledRm04At S basisAt iota t x)
      rw [← h1]
      dsimp [f]
      exact pulledRm_norm_eq_rm_norm (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht x
    calc
      ‖uhlenbeckPulledRm04At S basisAt iota t x‖ = f (t, x) := heq
      _ ≤ R := hle
      _ ≤ max R 0 := le_max_left _ _

private noncomputable def intrinsicFiberInfDist
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (K τ : ℝ) (x : M) : ℝ :=
  letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
    (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
  letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
  letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
  Metric.infDist (uhlenbeckPulledRm04At S basisAt iota τ x)
    (fiberHamiltonIveyRegion basisAt K τ x)

omit [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)] in
private theorem intrinsicFiberInfDist_eq_two_mul_matrixInfDist
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (K : ℝ) {q : ℝ × M}
    (hq : q ∈ Set.Icc 0 T ×ˢ (Set.univ : Set M))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (hK : 0 < K) :
    intrinsicFiberInfDist hT S basisAt iota K q.1 q.2 =
      2 * Metric.infDist (matrixToEuclidean (fun i j : Fin 3 =>
          tensor04StandardAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
            (basisAt q.2 (bivectorIndex3 i).1) (basisAt q.2 (bivectorIndex3 i).2)
            (basisAt q.2 (bivectorIndex3 j).2) (basisAt q.2 (bivectorIndex3 j).1)))
        (hamiltonIveyConvexMatrixRegionEuclidean K q.1) := by
  let : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) q.2) :=
    (tensor0SMetricData (I := I) (S.base.metric 0) q.2 4).toCore
  let : NormedAddCommGroup (Tensor04At (I := I) (M := M) q.2) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) q.2)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) q.2 4).toCore
  let : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) q.2) :=
    @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) q.2)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) q.2 4).toCore.toCore
  change Metric.infDist (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
      (fiberHamiltonIveyRegion basisAt K q.1 q.2) =
    2 * Metric.infDist (matrixToEuclidean (fun i j : Fin 3 =>
        tensor04StandardAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
          (basisAt q.2 (bivectorIndex3 i).1) (basisAt q.2 (bivectorIndex3 i).2)
          (basisAt q.2 (bivectorIndex3 j).2) (basisAt q.2 (bivectorIndex3 j).1)))
      (hamiltonIveyConvexMatrixRegionEuclidean K q.1)
  have hqτ : 0 ≤ q.1 := hq.1.1
  have hm : uhlenbeckPulledRm04At S basisAt iota q.1 q.2 ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) q.2 :=
    uhlenbeckPulledRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (M := M) S basisAt iota q.1 q.2
  exact infDist_fiberHamiltonIveyRegion_eq_two_mul_matrixInfDist_of_orthonormal (I := I) (M := M)
    (S.base.metric 0) q.2 basisAt (horth0 q.2) hK hqτ
    (uhlenbeckPulledRm04At S basisAt iota q.1 q.2) hm

omit [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M]
    [NeZero (Module.finrank ℝ E)] in
private noncomputable def intrinsicFrameIndex
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (x : M) (a : Fin 3) : Fin (Module.finrank ℝ E) :=
  ⟨a.val, by
    have hfe : Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I x) := by
      have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]
        exact mem_chart_source H x
      exact ((trivializationAt E (TangentSpace I) x).linearEquivAt ℝ x hx).finrank_eq.symm
    rw [hfe, hdim x]
    exact a.isLt⟩

omit [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def intrinsicFlowFrame
    (g : SmoothRiemannianMetric I M)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (α : M) (q : ℝ × M) (a : Fin 3) : TangentSpace I q.2 :=
  chartFrameNorm (I := I) g α (intrinsicFrameIndex (I := I) hdim q.2 a) q.2

omit [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def flowFrameOperatorMatrix
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (α : M) (q : ℝ × M) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
      (intrinsicFlowFrame (I := I) (S.base.metric q.1) hdim α q (bivectorIndex3 i).1)
      (intrinsicFlowFrame (I := I) (S.base.metric q.1) hdim α q (bivectorIndex3 i).2)
      (intrinsicFlowFrame (I := I) (S.base.metric q.1) hdim α q (bivectorIndex3 j).2)
      (intrinsicFlowFrame (I := I) (S.base.metric q.1) hdim α q (bivectorIndex3 j).1)

omit [SigmaCompactSpace M] in
private theorem intrinsicFiberInfDist_eq_two_mul_flowFrameMatrixInfDist
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (α : M) {K : ℝ} (hK : 0 < K) {q : ℝ × M}
    (hq : q ∈ Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) :
    intrinsicFiberInfDist hT S basisAt iota K q.1 q.2 =
      2 * Metric.infDist (matrixToEuclidean (flowFrameOperatorMatrix (I := I) hT S hdim α q))
        (hamiltonIveyConvexMatrixRegionEuclidean K q.1) := by
  classical
  let gτ : SmoothRiemannianMetric I M := S.base.metric q.1
  let e : Fin 3 → TangentSpace I q.2 :=
    fun a => intrinsicFlowFrame (I := I) gτ hdim α q a
  have hU : q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    smoothOrthoOpen_subset_baseSet (I := I) (M := M) α hq.2
  have hidx_inj : Function.Injective (intrinsicFrameIndex (I := I) hdim q.2) := by
    intro a b h
    apply Fin.ext
    simpa only [intrinsicFrameIndex] using
      (congrArg (fun i : Fin (Module.finrank ℝ E) => i.val) h)
  have horth_e : ∀ a b : Fin 3, gτ.inner q.2 (e a) (e b) = if a = b then 1 else 0 := by
    intro a b
    have horth := chartFrameNorm_orthonormal (I := I) gτ α hU
      (intrinsicFrameIndex (I := I) hdim q.2 a) (intrinsicFrameIndex (I := I) hdim q.2 b)
    change gτ.inner q.2
        (chartFrameNorm (I := I) gτ α (intrinsicFrameIndex (I := I) hdim q.2 a) q.2)
        (chartFrameNorm (I := I) gτ α (intrinsicFrameIndex (I := I) hdim q.2 b) q.2) =
      if a = b then 1 else 0
    rw [horth]
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (by rw [hab])]
    · rw [if_neg hab, if_neg (fun h => hab (hidx_inj h))]
  have hli : LinearIndependent ℝ e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hpair : gτ.inner q.2 (∑ j, c j • e j) (e i) = 0 := by
      rw [hc]
      simp
    rw [map_sum, sum_apply] at hpair
    rw [Finset.sum_eq_single i] at hpair
    · rw [ContinuousLinearMap.map_smul, smul_apply,
        horth_e i i, if_pos rfl, smul_eq_mul, mul_one] at hpair
      exact hpair
    · intro j _ hji
      rw [ContinuousLinearMap.map_smul, smul_apply,
        horth_e j i, if_neg (by simpa using hji), smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (TangentSpace I q.2) := by
    rw [Fintype.card_fin, hdim q.2]
  have hsp : Submodule.span ℝ (Set.range e) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank hcard
  let gsb : Module.Basis (Fin 3) ℝ (TangentSpace I q.2) := Module.Basis.mk hli hsp.symm.le
  have hgsb : (gsb : Fin 3 → TangentSpace I q.2) = e := by
    funext a
    exact Module.Basis.mk_apply hli hsp.symm.le a
  have horth_gsb : OrthonormalBasisAt (I := I) gτ q.2 gsb := by
    intro i j
    rw [hgsb]
    simpa [delta3] using horth_e i j
  have ht : q.1 ∈ Set.Icc 0 T := hq.1
  let mov : Module.Basis (Fin 3) ℝ (TangentSpace I q.2) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram q.1 ht q.2
  have horth_mov : OrthonormalBasisAt (I := I) gτ q.2 mov := by
    simpa [mov, gτ] using uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M)
      hT S basisAt iota hiota0 hgram q.2 (horth0 q.2) ht
  have hstep1 : intrinsicFiberInfDist hT S basisAt iota K q.1 q.2 =
      2 * Metric.infDist
        (matrixToEuclidean (tensor04CurvatureOperatorMatrixAt (I := I) (basisAt q.2)
          (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)))
        (hamiltonIveyConvexMatrixRegionEuclidean K q.1) := by
    have hdist := intrinsicFiberInfDist_eq_two_mul_matrixInfDist (I := I) (M := M)
      hT S basisAt iota K (q := q) (by exact ⟨hq.1, trivial⟩) horth0 hK
    have hmatrix : (fun i j =>
        tensor04StandardAt (I := I) (M := M)
          (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
          ((basisAt q.2) (bivectorIndex3 i).1)
            ((basisAt q.2) (bivectorIndex3 i).2)
            ((basisAt q.2) (bivectorIndex3 j).2)
            ((basisAt q.2) (bivectorIndex3 j).1)) =
      tensor04CurvatureOperatorMatrixAt (I := I) (basisAt q.2)
        (uhlenbeckPulledRm04At S basisAt iota q.1 q.2) := by
      ext i j
      rfl
    rw [hmatrix] at hdist
    exact hdist
  have hstep2 : tensor04CurvatureOperatorMatrixAt (I := I) (basisAt q.2)
        (uhlenbeckPulledRm04At S basisAt iota q.1 q.2) =
      tensor04CurvatureOperatorMatrixAt (I := I) mov (S.base.rm04 q.1 q.2) := by
    have hcurv := curvatureOperatorMatrixAt_pulledTensor_eq_original_moving
      (I := I) (M := M) hT S basisAt iota hiota0 hgram ht q.2
    change tensor04CurvatureOperatorMatrixAt (I := I) (basisAt q.2)
        (uhlenbeckPulledRm04At S basisAt iota q.1 q.2) =
      tensor04CurvatureOperatorMatrixAt (I := I)
        (uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram q.1 ht q.2)
        (S.base.rm04 q.1 q.2) at hcurv
    simpa only [mov] using hcurv
  have hstep3 : Metric.infDist
        (matrixToEuclidean (tensor04CurvatureOperatorMatrixAt (I := I) mov (S.base.rm04 q.1 q.2)))
        (hamiltonIveyConvexMatrixRegionEuclidean K q.1) =
      Metric.infDist
        (matrixToEuclidean (tensor04CurvatureOperatorMatrixAt (I := I) gsb (S.base.rm04 q.1 q.2)))
        (hamiltonIveyConvexMatrixRegionEuclidean K q.1) :=
    curvatureOperatorMatrixEuclidean_infDist_eq_of_orthonormal_bases
      (I := I) (M := M) gτ q.2 mov gsb
      horth_mov horth_gsb
      ⟨S.base.rm04 q.1 q.2, metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) gτ q.2⟩
      hK hq.1.1
  have hstep4 : tensor04CurvatureOperatorMatrixAt (I := I) gsb (S.base.rm04 q.1 q.2) =
      flowFrameOperatorMatrix (I := I) hT S hdim α q := by
    ext i j
    simp [flowFrameOperatorMatrix, hgsb, e, gτ]
  calc
    intrinsicFiberInfDist hT S basisAt iota K q.1 q.2
        = 2 * Metric.infDist
            (matrixToEuclidean (tensor04CurvatureOperatorMatrixAt (I := I) (basisAt q.2)
              (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)))
            (hamiltonIveyConvexMatrixRegionEuclidean K q.1) := hstep1
    _ = 2 * Metric.infDist
            (matrixToEuclidean (tensor04CurvatureOperatorMatrixAt (I := I) mov (S.base.rm04 q.1 q.2)))
            (hamiltonIveyConvexMatrixRegionEuclidean K q.1) := by rw [hstep2]
    _ = 2 * Metric.infDist
            (matrixToEuclidean (tensor04CurvatureOperatorMatrixAt (I := I) gsb (S.base.rm04 q.1 q.2)))
            (hamiltonIveyConvexMatrixRegionEuclidean K q.1) := by rw [hstep3]
    _ = 2 * Metric.infDist (matrixToEuclidean (flowFrameOperatorMatrix (I := I) hT S hdim α q))
            (hamiltonIveyConvexMatrixRegionEuclidean K q.1) := by rw [hstep4]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
private lemma flowFrameOperatorMatrix_continuousOn_local
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (α : M) :
    ContinuousOn (fun q : ℝ × M =>
      matrixToEuclidean (flowFrameOperatorMatrix (I := I) hT S hdim α q))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) := by
  classical
  let U : Set M := smoothOrthoOpen (I := I) (M := M) α
  have hU_base : ∀ q : ℝ × M, q ∈ Set.Icc 0 T ×ˢ U →
      q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro q hq
    exact smoothOrthoOpen_subset_baseSet (I := I) (M := M) α hq.2
  let e (a : Fin 3) (q : ℝ × M) : TangentSpace I q.2 :=
    intrinsicFlowFrame (I := I) (S.base.metric q.1) hdim α q a
  have he_cont : ∀ a : Fin 3,
      ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2 (e a q))
        (Set.Icc 0 T ×ˢ U) := by
    intro a
    have hmain := chartFrameNorm_continuousOn_ricciFlow (I := I) (M := M) hT S hS α
      (intrinsicFrameIndex (I := I) hdim α a)
    refine hmain.congr ?_
    intro q hq
    change TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2
        (chartFrameNorm (I := I) (S.base.metric q.1) α
          (intrinsicFrameIndex (I := I) hdim q.2 a) q.2) =
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2
        (chartFrameNorm (I := I) (S.base.metric q.1) α
          (intrinsicFrameIndex (I := I) hdim α a) q.2)
    apply congrArg (fun i : Fin (Module.finrank ℝ E) =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2
        (chartFrameNorm (I := I) (S.base.metric q.1) α i q.2))
    apply Fin.ext
    rfl
  have hentry4 : ∀ a b c d : Fin 3,
      ContinuousOn (fun q : ℝ × M =>
        tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e a q) (e b q) (e c q) (e d q))
        (Set.Icc 0 T ×ˢ U) := by
    intro a b c d
    have hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 (Set.Icc 0 T)
        (fun t x => S.base.rm04 t x) := by
      exact tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
        hS.rm04Cont (by intro s hs; exact hs)
    rw [continuousOn_iff_continuous_domRestrict]
    let P := {q : ℝ × M // q ∈ Set.Icc 0 T ×ˢ U}
    have heval := tensor0SFamilyContinuousOnSet.eval_continuous (I := I) (M := M) (s := 4)
      (K := Set.Icc 0 T) (A := fun t x => S.base.rm04 t x) hA
      (P := P) (τ := fun p : P => p.1.1) (b := fun p : P => p.1.2)
      (continuous_fst.comp continuous_subtype_val) (fun p : P => p.2.1)
      (continuous_snd.comp continuous_subtype_val)
      (v := fun n : Fin 4 => fun p : P =>
        if n = 0 then e a p.1 else if n = 1 then e b p.1 else if n = 2 then e c p.1 else e d p.1)
      (by
        intro n
        fin_cases n
        · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
          change Continuous ((Set.Icc 0 T ×ˢ U).domRestrict fun q : ℝ × M =>
            TotalSpace.mk' E q.2 (e a q))
          exact continuousOn_iff_continuous_domRestrict.mp (he_cont a)
        · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
          change Continuous ((Set.Icc 0 T ×ˢ U).domRestrict fun q : ℝ × M =>
            TotalSpace.mk' E q.2 (e b q))
          exact continuousOn_iff_continuous_domRestrict.mp (he_cont b)
        · simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          change Continuous ((Set.Icc 0 T ×ˢ U).domRestrict fun q : ℝ × M =>
            TotalSpace.mk' E q.2 (e c q))
          exact continuousOn_iff_continuous_domRestrict.mp (he_cont c)
        · simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          change Continuous ((Set.Icc 0 T ×ˢ U).domRestrict fun q : ℝ × M =>
            TotalSpace.mk' E q.2 (e d q))
          exact continuousOn_iff_continuous_domRestrict.mp (he_cont d))
    refine heval.congr (fun p => ?_)
    change (S.base.rm04 p.1.1 p.1.2)
        (fun n : Fin 4 => if n = 0 then e a p.1 else if n = 1 then e b p.1 else if n = 2 then e c p.1 else e d p.1) =
      tensor04StandardAt (I := I) (M := M) (S.base.rm04 p.1.1 p.1.2)
        (e a p.1) (e b p.1) (e c p.1) (e d p.1)
    rw [tensor04StandardAt]
    congr 1
  have hmat_local : ContinuousOn (fun q : ℝ × M =>
      matrixToEuclidean (fun i j : Fin 3 =>
        tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
          (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q)))
      (Set.Icc 0 T ×ˢ U) := by
    have hfun : ContinuousOn (fun q : ℝ × M =>
        fun ij : Fin 3 × Fin 3 =>
        tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 ij.1).1 q) (e (bivectorIndex3 ij.1).2 q)
          (e (bivectorIndex3 ij.2).2 q) (e (bivectorIndex3 ij.2).1 q))
        (Set.Icc 0 T ×ˢ U) := by
      rw [continuousOn_iff_continuous_domRestrict]
      let P := {q : ℝ × M // q ∈ Set.Icc 0 T ×ˢ U}
      exact continuous_pi (by
        intro ij
        change Continuous ((Set.Icc 0 T ×ˢ U).domRestrict fun q : ℝ × M =>
          tensor04StandardAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
            (e (bivectorIndex3 ij.1).1 q) (e (bivectorIndex3 ij.1).2 q)
            (e (bivectorIndex3 ij.2).2 q) (e (bivectorIndex3 ij.2).1 q))
        exact continuousOn_iff_continuous_domRestrict.mp
          (hentry4 (bivectorIndex3 ij.1).1 (bivectorIndex3 ij.1).2
            (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1))
    exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 × Fin 3 => ℝ)).comp_continuousOn hfun
  refine hmat_local.congr ?_
  intro q hq
  apply congrArg matrixToEuclidean
  ext i j
  rfl

omit [SigmaCompactSpace M] in
private lemma fiberInfDist_continuousOn_local
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (α : M) {K : ℝ} (hK : 0 < K) :
    ContinuousOn (fun q : ℝ × M => intrinsicFiberInfDist hT S basisAt iota K q.1 q.2)
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) := by
  classical
  let m : ℝ × M → EuclideanSpace ℝ (Fin 3 × Fin 3) := fun q =>
    matrixToEuclidean (flowFrameOperatorMatrix (I := I) hT S hdim α q)
  have hm_cont : ContinuousOn m (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) := by
    simpa [m] using flowFrameOperatorMatrix_continuousOn_local (I := I) (M := M) hT S hS hdim α
  have hg : ContinuousOn (fun r : ℝ × (EuclideanSpace ℝ (Fin 3 × Fin 3)) =>
      Metric.infDist r.2 (hamiltonIveyConvexMatrixRegionEuclidean K r.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3 × Fin 3)))) :=
    continuousOn_infDist_hamiltonIveyRegion hK
  have hh : ContinuousOn (fun q : ℝ × M => (q.1, m q))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) :=
    (continuous_fst.continuousOn).prodMk hm_cont
  have hmaps : Set.MapsTo (fun q : ℝ × M => (q.1, m q))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α)
      (Set.Icc 0 T ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3 × Fin 3)))) := by
    intro q hq
    exact ⟨hq.1, trivial⟩
  have hcomp : ContinuousOn (fun q : ℝ × M =>
      Metric.infDist ((q.1, m q)).2 (hamiltonIveyConvexMatrixRegionEuclidean K ((q.1, m q)).1))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) :=
    hg.comp' hh hmaps
  have htwo : ContinuousOn (fun q : ℝ × M =>
      2 * Metric.infDist ((q.1, m q)).2 (hamiltonIveyConvexMatrixRegionEuclidean K ((q.1, m q)).1))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) :=
    (continuousOn_const.mul hcomp)
  refine htwo.congr ?_
  intro q hq
  simpa [m] using intrinsicFiberInfDist_eq_two_mul_flowFrameMatrixInfDist (I := I) (M := M)
    hT S basisAt iota hiota0 hgram horth0 hdim α hK (q := q) hq

omit [SigmaCompactSpace M] in
private theorem fiberInfDist_continuousOn_intrinsic
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    {K : ℝ} (hK : 0 < K) :
    ContinuousOn (fun q : ℝ × M => intrinsicFiberInfDist hT S basisAt iota K q.1 q.2)
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
  classical
  intro q hq
  let α : M := q.2
  have hlocal := fiberInfDist_continuousOn_local (I := I) (M := M) hT S hS hdim basisAt horth0 iota
    hiota0 hgram α hK
  have hqL : q ∈ Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α := by
    exact ⟨hq.1, mem_smoothOrthoOpen (I := I) (M := M) α⟩
  have hL : ContinuousWithinAt
      (fun r : ℝ × M => intrinsicFiberInfDist hT S basisAt iota K r.1 r.2)
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) q :=
    hlocal.continuousWithinAt hqL
  have hmem_nhds : (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) ∈
      𝓝[(Set.Icc 0 T ×ˢ (Set.univ : Set M))] q := by
    rw [mem_nhdsWithin]
    refine ⟨Set.univ ×ˢ smoothOrthoOpen (I := I) (M := M) α, ?_, ?_, ?_⟩
    · exact isOpen_univ.prod (smoothOrthoOpen_open (I := I) (M := M) α)
    · exact ⟨trivial, mem_smoothOrthoOpen (I := I) (M := M) α⟩
    · intro r hr
      have hEq : (Set.univ ×ˢ smoothOrthoOpen (I := I) (M := M) α) ∩
          (Set.Icc 0 T ×ˢ (Set.univ : Set M)) =
          Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α := by
        rw [Set.prod_inter_prod]
        simp
      exact (hEq ▸ hr)
  have heq : 𝓝[(Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α)] q =
      𝓝[(Set.Icc 0 T ×ˢ (Set.univ : Set M))] q := by
    apply le_antisymm
    · exact nhdsWithin_mono q (by
        intro r hr
        exact Set.mem_prod.mpr ⟨(Set.mem_prod.mp hr).1, trivial⟩)
    · exact (nhdsWithin_le_iff (s := (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
        (t := (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α)) (x := q)).mpr hmem_nhds
  change Tendsto (fun r : ℝ × M =>
      intrinsicFiberInfDist hT S basisAt iota K r.1 r.2)
    (𝓝[(Set.Icc 0 T ×ˢ (Set.univ : Set M))] q)
    (𝓝 (intrinsicFiberInfDist hT S basisAt iota K q.1 q.2))
  rw [← heq]
  exact hL

omit [SigmaCompactSpace M] in
theorem continuousOn_infDist_uhlenbeckPulledRm04At_fiberHamiltonIveyRegion
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    {K : ℝ} (hK : 0 < K) :
    ContinuousOn (fun q : ℝ × M =>
      letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) q.2) :=
        (tensor0SMetricData (I := I) (S.base.metric 0) q.2 4).toCore
      letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) q.2) :=
        @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) q.2)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) q.2 4).toCore
      letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) q.2) :=
        @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) q.2)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) q.2 4).toCore.toCore
      Metric.infDist (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
        (fiberHamiltonIveyRegion basisAt K q.1 q.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
  classical
  have h := fiberInfDist_continuousOn_intrinsic
    (I := I) (M := M) hT S hS hdim basisAt horth0 iota hiota0 hgram hK
  refine h.congr ?_
  intro q hq
  simp [intrinsicFiberInfDist]
end DifferentialGeometry.PDE.RicciFlow

end
