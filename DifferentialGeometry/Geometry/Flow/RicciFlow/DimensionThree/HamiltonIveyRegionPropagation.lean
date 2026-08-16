import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyCurvatureEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ConvexTimeDep

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Filter
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Dim3Reaction
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem uhlenbeckCurvatureOperatorMatrix_mem_hamiltonIveyRegion
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {T K : ℝ} (hK : 0 < K) (hT : 0 < T)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (pulledRm roughLapD B : FourComp M (Fin 3))
    (hU : UhlenbeckCurvatureEvolutionInFrameOn (D := D) pulledRm roughLapD B)
    (hlap : ∀ t : Real, t ∈ D.carrier → ∀ x : M, ∀ ij : Fin 3 × Fin 3,
      roughLapD t x (bivectorIndex3 ij.1).1 (bivectorIndex3 ij.1).2
          (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1 =
        laplacianAt (I := I) G t
          (fun y : M => uhlenbeckCurvatureOperatorMatrix pulledRm t y ij) x)
    (hjoint : ContinuousOn (fun q : Real × M => uhlenbeckCurvatureOperatorMatrix pulledRm q.1 q.2)
      (D.carrier ×ˢ (Set.univ : Set M)))
    (hsmooth : ∀ ij : Fin 3 × Fin 3, ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞
        (fun x : M => uhlenbeckCurvatureOperatorMatrix pulledRm t x ij))
    (R : Real → M → Fin 3 → Fin 3 → ℝ)
    (hR : ∀ t x i j, R t x i j = R t x j i)
    (hrm : ∀ t x a b c d, pulledRm t x a b c d = rm (R t x) a b c d)
    (hB : ∀ t x a b c d, B t x a b c d = bTensorDown (fun a' b' c' d' => pulledRm t x a' b' c' d') a b c d)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hbound : ∃ R : ℝ, 0 ≤ R ∧ ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      ‖uhlenbeckCurvatureOperatorMatrix pulledRm t x‖ ≤ R)
    (hCdist_cont : ContinuousOn
      (fun q : Real × M => Metric.infDist (uhlenbeckCurvatureOperatorMatrix pulledRm q.1 q.2)
        (hamiltonIveyConvexMatrixRegionEuclid K q.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
    (hinit : ∀ x : M, uhlenbeckCurvatureOperatorMatrix pulledRm 0 x ∈
      hamiltonIveyConvexMatrixRegionEuclid K 0) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      uhlenbeckCurvatureOperatorMatrix pulledRm t x ∈ hamiltonIveyConvexMatrixRegionEuclid K t := by
  let C : Real → Set (EuclideanSpace ℝ (Fin 3 × Fin 3)) :=
    fun t => hamiltonIveyConvexMatrixRegionEuclid K (max t 0)
  let N : Set (EuclideanSpace ℝ (Fin 3 × Fin 3)) :=
    {ν | (symmEuclid_isHermitian ν).eigenvalues₀ 0 < 0 ∨ symmEuclid ν = 0}
  let support : Real → EuclideanSpace ℝ (Fin 3 × Fin 3) → ℝ :=
    fun t ν => hamiltonIveyConvexMatrixRegionSupportEuclid K (max t 0) ν
  let support' : Real → EuclideanSpace ℝ (Fin 3 × Fin 3) → ℝ :=
    fun t ν => hamiltonIveyConvexMatrixRegionSupportDeriv K hK t ν
  let reaction : Real → M → EuclideanSpace ℝ (Fin 3 × Fin 3) →
      EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    fun _ _ A => uhlenbeckCurvatureOperatorReactionState A
  let u : Real → M → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    fun t x => uhlenbeckCurvatureOperatorMatrix pulledRm t x
  have hU_closed : UhlenbeckCurvatureEvolutionInFrameOn
      (D := RealTimeInterval.closed 0 T hT.le) pulledRm roughLapD B := by
    intro t x a b c d
    have htreg : (t : Real) ∈ D.regular := hTreg ⟨t.2.1, le_of_lt t.2.2⟩
    have hderiv := hU ⟨(t : Real), htreg⟩ x a b c d
    have hmono : Set.Icc 0 T ⊆ D.carrier := hTsub
    exact hderiv.mono hmono
  have hsol : IsInnerProductHeatReactionOn (D := RealTimeInterval.closed 0 T hT.le) G reaction u := by
    have h := innerProductHeatReactionOn_of_uhlenbeckCurvatureOperator_quadratic
      (D := RealTimeInterval.closed 0 T hT.le) G pulledRm roughLapD B
      hU_closed
      (fun t ht x ij => hlap t (hTsub ht) x ij)
      (hjoint.mono (by intro q hq; exact ⟨hTsub hq.1, hq.2⟩))
      (fun ij t ht => hsmooth ij t (hTsub ht))
      R hR hrm hB
    simpa [reaction, u] using h
  have hCclosed : ∀ t : Real, IsClosed (C t) := by
    intro t
    dsimp [C]
    exact isClosed_hamiltonIveyConvexMatrixRegionEuclid hK
  have hCconvex : ∀ t : Real, Convex ℝ (C t) := by
    intro t
    dsimp [C]
    exact convex_hamiltonIveyConvexMatrixRegionEuclid hK (le_max_right t 0)
  have hCne : ∀ t : Real, (C t).Nonempty := by
    intro t
    dsimp [C]
    exact nonempty_hamiltonIveyConvexMatrixRegionEuclid hK (le_max_right t 0)
  have hCzero : ∀ t : Real, (0 : EuclideanSpace ℝ (Fin 3 × Fin 3)) ∈ C t := by
    intro t
    dsimp [C]
    exact zero_mem_hamiltonIveyConvexMatrixRegionEuclid hK (le_max_right t 0)
  have hsupp : ∀ t p, p ∈ C t ↔
      ∀ ν : EuclideanSpace ℝ (Fin 3 × Fin 3), ν ∈ N → inner ℝ ν p ≤ support t ν := by
    intro t p
    have hτ : 0 ≤ max t 0 := le_max_right t 0
    have hiff := hamiltonIveyConvexMatrixRegionEuclid_mem_iff_forall_support_le
      (K := K) (τ := max t 0) hK hτ p
    constructor
    · intro hp ν hν
      have hfs : ν ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclid K (max t 0)) := by
        rw [mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ]
        exact hν
      have hle := hiff.mp (by simpa [C] using hp) ν hfs
      simpa [support] using hle
    · intro h
      have hpC : p ∈ hamiltonIveyConvexMatrixRegionEuclid K (max t 0) := by
        refine hiff.mpr ?_
        intro ν hfs
        have hνN : ν ∈ N := by
          exact (mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ ν).mp hfs
        have hle := h ν hνN
        simpa [support] using hle
      simpa [C] using hpC
  have hsupport_sup : ∀ t ν, ν ∈ N →
      support t ν = sSup {x : ℝ | ∃ q : EuclideanSpace ℝ (Fin 3 × Fin 3),
        q ∈ C t ∧ x = inner ℝ ν q} := by
    intro t ν hν
    have hτ : 0 ≤ max t 0 := le_max_right t 0
    have hfs : ν ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclid K (max t 0)) := by
      rw [mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ]
      exact hν
    have hEq := hamiltonIveyConvexMatrixRegionSupportEuclid_eq_supportFunction_of_finiteSupportDirections
      hK hτ ν hfs
    unfold supportFunction at hEq
    simpa [support, C] using hEq
  have hNnormal : ∀ t p, p ∈ C t → ∀ ν : EuclideanSpace ℝ (Fin 3 × Fin 3),
      (∀ q : EuclideanSpace ℝ (Fin 3 × Fin 3), q ∈ C t → inner ℝ ν (q - p) ≤ 0) → ν ∈ N := by
    intro t p hp ν hnormal
    have hfs : ν ∈ finiteSupportDirections (C t) := mem_finiteSupportDirections_of_normal hnormal
    have hτ : 0 ≤ max t 0 := le_max_right t 0
    exact (mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ ν).mp (by simpa [C] using hfs)
  rcases hbound with ⟨R₀, hR₀, hbound'⟩
  rcases uhlenbeckCurvatureOperatorReactionState_lipschitzOn_closedBall (2 * R₀) (by linarith)
    with ⟨L, hL⟩
  have hL' : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzOnWith L (reaction t x) (Metric.closedBall 0 (2 * R₀)) := by
    intro t ht x
    simpa [reaction] using hL
  have hCdist_cont' : ContinuousOn
      (fun q : Real × M => Metric.infDist (u q.1 q.2) (C q.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
    refine hCdist_cont.congr ?_
    intro q hq
    have hmax : max q.1 0 = q.1 := max_eq_left hq.1.1
    simp [C, u, hmax]
  have hsupport_cont : ∀ ν : EuclideanSpace ℝ (Fin 3 × Fin 3), ν ∈ N →
      ContinuousOn (fun t : Real => support t ν) (Set.Icc 0 T) := by
    intro ν hν
    rcases hν with hvneg | hsymm
    · have hc := hamiltonIveyConvexMatrixRegionSupportEuclid_continuousOn (K := K) (T := T) hK ν hvneg
      refine hc.congr ?_
      intro t ht
      have hmax : max t 0 = t := max_eq_left ht.1
      simp [support, hmax]
    · have hz : ∀ t : ℝ, support t ν = 0 := by
        intro t
        dsimp [support]
        exact hamiltonIveyConvexMatrixRegionSupportEuclid_eq_zero_of_symm_zero (K := K) (τ := max t 0) ν hsymm
      simpa [hz] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc 0 T))
  have hsupport_time : ∀ ν : EuclideanSpace ℝ (Fin 3 × Fin 3), ν ∈ N →
      ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t →
        HasDerivAt (fun s : Real => support s ν) (support' t ν) t := by
    intro ν hν t ht hpos
    rcases hν with hvneg | hsymm
    · have hd := hamiltonIveyConvexMatrixRegionSupportEuclid_hasDerivAt
        (K := K) (τ₀ := t) hK hpos ν
      have hnhd : (fun s : ℝ => support s ν) =ᶠ[𝓝 t]
          fun s : ℝ => hamiltonIveyConvexMatrixRegionSupportEuclid K s ν := by
        have hpos_nhd : ∀ᶠ s in 𝓝 t, 0 < s := Ioi_mem_nhds hpos
        filter_upwards [hpos_nhd] with s hs
        have hmax : max s 0 = s := max_eq_left (le_of_lt hs)
        simp [support, hmax]
      have hmain := hd.congr_of_eventuallyEq hnhd
      simpa [support'] using hmain
    · have hz : ∀ s : ℝ, support s ν = 0 := by
        intro s
        dsimp [support]
        exact hamiltonIveyConvexMatrixRegionSupportEuclid_eq_zero_of_symm_zero (K := K) (τ := max s 0) ν hsymm
      have hd : HasDerivAt (fun s : ℝ => support s ν) 0 t := by
        simpa [hz] using (hasDerivAt_const (x := t) (c := (0 : ℝ)))
      have hderiv' : hamiltonIveyConvexMatrixRegionSupportDeriv K hK t ν = 0 :=
        hamiltonIveyConvexMatrixRegionSupportDeriv_eq_zero_of_symm_zero hK t ν hsymm
      simpa [support', hderiv'] using hd
  have htangent : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M,
      ∀ p : EuclideanSpace ℝ (Fin 3 × Fin 3), p ∈ C t →
      ∀ ν : EuclideanSpace ℝ (Fin 3 × Fin 3), ν ∈ N →
        support t ν = inner ℝ ν p →
          inner ℝ (reaction t x p) ν ≤ support' t ν := by
    intro t ht hpos x p hp ν hν hsupportEq
    change (symmEuclid_isHermitian ν).eigenvalues₀ 0 < 0 ∨ symmEuclid ν = 0 at hν
    rcases hν with hvneg | hsymm
    · have ht0 : 0 ≤ t := ht.1
      have hsupp_eq' : hamiltonIveyConvexMatrixRegionSupportEuclid K t ν = inner ℝ ν p := by
        have hmax : max t 0 = t := max_eq_left ht.1
        simpa [support, hmax] using hsupportEq
      have hp' : p ∈ hamiltonIveyConvexMatrixRegionEuclid K t := by
        have hmax : max t 0 = t := max_eq_left ht.1
        simpa [C, hmax] using hp
      have hd := hamiltonIveyConvexMatrixRegionSupportEuclid_hasDerivAt
        (K := K) (τ₀ := t) hK hpos ν
      have hmain := hamiltonIveyConvexMatrixRegionSupportEuclid_reaction_le_deriv
        hK ht.1 ν hvneg p hp' hsupp_eq' (support' t ν)
        (by simpa [support'] using hd)
      simpa [reaction] using hmain
    · have hp' : p ∈ hamiltonIveyConvexMatrixRegionEuclid K (max t 0) := by
        simpa [C] using hp
      have hpm : euclidToMatrix p ∈ hamiltonIveyConvexMatrixRegion K (max t 0) :=
        (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K (max t 0) p).1 hp'
      have hpAh : (euclidToMatrix p).IsHermitian := by
        rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hpm
        exact hpm.1
      have hinner0 : inner ℝ (reaction t x p) ν = 0 := by
        dsimp [reaction]
        exact inner_reactionState_zero_of_symm_zero ν p hsymm hpAh
      have hderiv' : support' t ν = 0 := by
        dsimp [support']
        exact hamiltonIveyConvexMatrixRegionSupportDeriv_eq_zero_of_symm_zero hK t ν hsymm
      rw [hinner0, hderiv']
  have hmain := closed_convex_timeDep_heat_reaction_mem_of_support_tangent
    (I := I) (M := M) G hT C N support support'
    hCclosed hCconvex hCne hsupp hsupport_sup hNnormal
    reaction u hsol R₀ hbound' hCzero L hL' hCdist_cont'
    hsupport_cont hsupport_time htangent (by
      intro x
      dsimp [C, u]
      simpa using hinit x)
  intro t ht x
  have hmem := hmain t ht x
  have hmax : max t 0 = t := max_eq_left ht.1
  simpa [C, u, hmax] using hmem

theorem curvatureOperatorRegionPropagationOn_of_uhlenbeckData
    [I.Boundaryless] [CompactSpace M] [T2Space M]
    [IsManifold I 1 M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {T K : ℝ} (hK : 0 < K) (hT : 0 < T)
    (pulledRm roughLapD B : FourComp M (Fin 3))
    (hU : UhlenbeckCurvatureEvolutionInFrameOn (D := D) pulledRm roughLapD B)
    (hlap : ∀ t : Real, t ∈ D.carrier → ∀ x : M, ∀ ij : Fin 3 × Fin 3,
      roughLapD t x (bivectorIndex3 ij.1).1 (bivectorIndex3 ij.1).2
          (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1 =
        laplacianAt (I := I) (flowG (I := I) S) t
          (fun y : M => uhlenbeckCurvatureOperatorMatrix pulledRm t y ij) x)
    (hjoint : ContinuousOn (fun q : Real × M => uhlenbeckCurvatureOperatorMatrix pulledRm q.1 q.2)
      (D.carrier ×ˢ (Set.univ : Set M)))
    (hsmooth : ∀ ij : Fin 3 × Fin 3, ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞
        (fun x : M => uhlenbeckCurvatureOperatorMatrix pulledRm t x ij))
    (R : Real → M → Fin 3 → Fin 3 → ℝ)
    (hR : ∀ t x i j, R t x i j = R t x j i)
    (hrm : ∀ t x a b c d, pulledRm t x a b c d = rm (R t x) a b c d)
    (hB : ∀ t x a b c d, B t x a b c d = bTensorDown (fun a' b' c' d' => pulledRm t x a' b' c' d') a b c d)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hbound : ∃ R : ℝ, 0 ≤ R ∧ ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      ‖uhlenbeckCurvatureOperatorMatrix pulledRm t x‖ ≤ R)
    (hCdist_cont : ContinuousOn
      (fun q : Real × M => Metric.infDist (uhlenbeckCurvatureOperatorMatrix pulledRm q.1 q.2)
        (hamiltonIveyConvexMatrixRegionEuclid K q.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
    (hinit : ∀ x : M, uhlenbeckCurvatureOperatorMatrix pulledRm 0 x ∈
      hamiltonIveyConvexMatrixRegionEuclid K 0)
    (hpull : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      ∃ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
        OrthonormalBasisAt (I := I) (S.base.metric t) x basis ∧
          ∀ a b c d : Fin 3,
            pulledRm t x a b c d =
              tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
                (basis a) (basis b) (basis c) (basis d)) :
    CurvatureOperatorRegionPropagationOn (I := I) (M := M) S K 0 T := by
  have hmain := uhlenbeckCurvatureOperatorMatrix_mem_hamiltonIveyRegion
    (I := I) (M := M) hK hT (flowG (I := I) S)
    pulledRm roughLapD B hU hlap hjoint hsmooth R hR hrm hB hTsub hTreg
    hbound hCdist_cont hinit
  intro t ht x
  have ht' : t ∈ Set.Icc 0 T := by simpa using ht
  have hmem := hmain t ht' x
  rcases hpull t ht' x with ⟨basis, horth, hpull'⟩
  let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  have hmat := uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt
    (I := I) (M := M) (x := x) (basis := basis) (A := A) (pulledRm := pulledRm) (t := t) hpull'
  have hu_eq : uhlenbeckCurvatureOperatorMatrix pulledRm t x =
      matrixToEuclid (curvatureOperatorMatrixAt (I := I) x basis A) := by
    have h1 := uhlenbeckCurvatureOperatorMatrix_eq_matrixToEuclid (pulledRm := pulledRm) (t := t) (x := x)
    rw [h1, hmat]
  have hmem' : matrixToEuclid (curvatureOperatorMatrixAt (I := I) x basis A) ∈
      hamiltonIveyConvexMatrixRegionEuclid K t := by
    rwa [hu_eq] at hmem
  have hmatmem : curvatureOperatorMatrixAt (I := I) x basis A ∈ hamiltonIveyConvexMatrixRegion K t := by
    rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff] at hmem'
    simpa [euclidToMatrix_matrixToEuclid] using hmem'
  simpa using ⟨basis, horth, hmatmem⟩
end DifferentialGeometry.PDE.RicciFlow

end
