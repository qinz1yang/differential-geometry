import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.PotentialIdentity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Rigidity.HeatPotential
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.RicciSoliton


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Entropy
open scoped ContDiff Manifold _root_.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] {D : RealTimeInterval}

theorem gradientRicciSoliton_and_hamiltonNormalized_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : M,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    {tau s : ℝ} (hs : 0 < s) (hstau : s < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) :
    ∃ hf : ContMDiff I 𝓘(ℝ) ∞ (fun y => redLength S T x y s),
      gradientRicciSoliton (I := I) (S.base.metric (T - s))
        ⟨fun y => redLength S T x y s, hf⟩ (1 / s) ∧
      hamiltonNormalized (I := I) (S.base.metric (T - s))
        ⟨fun y => redLength S T x y s, hf⟩ (1 / s) := by
  let a := s / 2
  let b := (s + tau) / 2
  have ha : 0 < a := by dsimp only [a]; linarith only [hs]
  have has : a < s := by dsimp only [a]; linarith only [hs]
  have hsb : s < b := by dsimp only [b]; linarith only [hstau]
  have hbtau : b < tau := by dsimp only [b]; linarith only [hstau]
  have hab : a < b := has.trans hsb
  let Dr := RealTimeInterval.closed a b hab.le
  let u := fun r y => redDensity S T x y r
  have hu := isHeatPotOn_redDensity_of_redVolume_eq_one
    S hS T hg x hRm ha hab hbtau hslab hvol
  have hpos : ∀ r, r ∈ Dr.regular ∩ Ioi (0 : ℝ) → ∀ y, 0 < u r y := by
    intro r _hr y
    exact Real.exp_pos _
  have hHJ : ∀ r, r ∈ Dr.regular → 0 < r → ∀ y : M,
      2 * deriv (fun q => perelmanPotential (Module.finrank ℝ E) q (u q) y) r +
        ((reverseFamily (flowG S) T).metric r).inner y
          (gradientFun (I := I) ((reverseFamily (flowG S) T).metric r)
            (perelmanPotential (Module.finrank ℝ E) r (u r)) y)
          (gradientFun (I := I) ((reverseFamily (flowG S) T).metric r)
            (perelmanPotential (Module.finrank ℝ E) r (u r)) y) -
        S.scalar (T - r) y + perelmanPotential (Module.finrank ℝ E) r (u r) y / r = 0 := by
    intro r hr hrpos y
    have hrtau : r < tau := hr.2.trans hbtau
    have hcoverage := lExp_inj_image_eq_univ_of_redVolume_eq_one
      S hS T hg x hRm hrpos hrtau hslab hvol
    have hy : y ∈ (fun Z : E => lExp S T x Z r) '' lInjDomain S T x r := by
      rw [hcoverage]
      exact mem_univ y
    obtain ⟨W, hW, hend⟩ := hy
    change lExp S T x W r = y at hend
    have hJ := redLength_HJ_of_rm S hS T hg x hRm hrpos hW
    rw [hend] at hJ
    have he : (fun q => perelmanPotential (Module.finrank ℝ E) q (u q) y) =ᶠ[𝓝 r]
        (fun q => redLength S T x y q) := by
      filter_upwards [eventually_gt_nhds hrpos] with q hq
      exact congrFun (perelmanPotential_redDensity S T x hq) y
    rw [he.deriv_eq, perelmanPotential_redDensity S T x hrpos]
    change 2 * deriv (fun q => redLength S T x y q) r +
      (S.base.metric (T - r)).inner y
        (gradientFun (I := I) (S.base.metric (T - r))
          (fun z => redLength S T x z r) y)
        (gradientFun (I := I) (S.base.metric (T - r))
          (fun z => redLength S T x z r) y) -
      S.scalar (T - r) y + redLength S T x y r / r = 0
    have hquot : redLength S T x y r / (2 * r) =
        (1 / 2 : ℝ) * (redLength S T x y r / r) := by ring
    rw [hquot] at hJ
    linarith only [hJ]
  have hsDr : s ∈ Dr.regular := ⟨has, hsb⟩
  have hTs : T - s ∈ D.regular :=
    hslab ⟨sub_le_sub_left hstau.le T, sub_le_self T hs.le⟩
  have h := Entropy.gradientRicciSoliton_and_hamiltonNormalized_of_hamilton_jacobi
    S hS T u hu hpos hsDr hs hTs hHJ
  have he : perelmanPotential (Module.finrank ℝ E) s (u s) =
      fun y => redLength S T x y s := perelmanPotential_redDensity S T x hs
  have hf := potential_slice Dr (reverseFamily (flowG S) T)
    (fun r y => -S.scalar (T - r) y) u (Module.finrank ℝ E) hu hsDr hs
    (hpos s ⟨hsDr, hs⟩)
  have hf' : ContMDiff I 𝓘(ℝ) ∞ (fun y => redLength S T x y s) := he ▸ hf
  refine ⟨hf', ?_⟩
  have hb : (⟨perelmanPotential (Module.finrank ℝ E) s (u s), hf⟩ :
      ContMDiffMap I 𝓘(ℝ) M ℝ ∞) = ⟨fun y => redLength S T x y s, hf'⟩ := by
    ext y
    exact congrFun he y
  change gradientRicciSoliton (I := I) (S.base.metric (T - s))
      ⟨perelmanPotential (Module.finrank ℝ E) s (u s), hf⟩ (1 / s) ∧
    hamiltonNormalized (I := I) (S.base.metric (T - s))
      ⟨perelmanPotential (Module.finrank ℝ E) s (u s), hf⟩ (1 / s) at h
  rw [hb] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Perelman
