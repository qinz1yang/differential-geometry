import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.ClosedIntervalRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureRank

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem exists_curvatureOperatorImageAt_finrank_eq_on_terminal_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular) (hdim : Module.finrank ℝ E = 3)
    (hR : ∀ t ∈ Icc a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∃ c ∈ Ioo a b, ∃ q : ℕ, (q = 0 ∨ q = 1 ∨ q = 3) ∧
      ∀ t ∈ Ioc c b, ∀ x,
        Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
          ⟨metricRm04At (S.family.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q := by
  let c := (a + b) / 2
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  let T := b - c
  have hT : 0 < T := sub_pos.mpr hcb
  let rank (t : ℝ) (x : M) : ℕ :=
    Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩)
  have hcarrier' : Icc (a - c) T ⊆ (D.timeShift c).carrier := by
    intro s hs
    change s + c ∈ D.carrier
    apply hcarrier
    dsimp [T] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hregular' : Ioo (a - c) T ⊆ (D.timeShift c).regular := by
    intro s hs
    change s + c ∈ D.regular
    apply hregular
    dsimp [T] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hR' : ∀ t ∈ Icc 0 T, ∀ x,
      (⟨metricRm04At ((S.timeShift c).family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          ((S.timeShift c).family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    intro t ht x
    apply hR (t + c)
    dsimp [T] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hclosed :=
    curvatureOperator_rank_spatially_constant_and_locally_constant_from_left_on_closed_interval
      (S.timeShift c) (isSolutionOn_timeShift hS c) (sub_neg.mpr hac) hT
      hcarrier' hregular' hdim hR'
  have hspace : ∀ t ∈ Ioc 0 T, ∀ x y, rank (t + c) x = rank (t + c) y := hclosed.1
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  obtain ⟨ε, hε, hstable⟩ := hclosed.2.2.1 T ⟨hT, le_rfl⟩ x₀
  have hstable' : ∀ s ∈ Ioc (T - ε) T, rank (s + c) x₀ = rank (T + c) x₀ :=
    hstable
  have haε : a < b - ε := by dsimp [T] at hε; linarith [hε.2]
  have hbε : b - ε < b := by linarith [hε.1]
  have hleft : ∀ t ∈ Ioc (b - ε) b, ∀ x, rank t x = rank b x₀ := by
    intro t ht x
    have hs : t - c ∈ Ioc 0 T := by
      dsimp [T] at hε ⊢
      constructor <;> linarith [hε.2, ht.1, ht.2]
    have hsε : t - c ∈ Ioc (T - ε) T := by
      dsimp [T]
      constructor <;> linarith [ht.1, ht.2]
    calc
      rank t x = rank (t - c + c) x := by rw [sub_add_cancel]
      _ = rank (t - c + c) x₀ := hspace _ hs x x₀
      _ = rank (T + c) x₀ := hstable' _ hsε
      _ = rank b x₀ := by dsimp [T]; rw [sub_add_cancel]
  refine ⟨b - ε, ⟨haε, hbε⟩, rank b x₀, ?_, hleft⟩
  have hmid : b - ε / 2 ∈ Ioc (b - ε) b := by
    constructor <;> linarith [hε.1]
  have hmidb : b - ε / 2 < b := by linarith [hε.1]
  have htri := curvatureOperatorImageAt_finrank_trichotomy_at_later_time S hS hdim
    hmid.1 (by intro r hr; exact hregular ⟨haε.trans_le hr.1, hr.2.trans_lt hmidb⟩)
    (by intro r hr; exact hR r ⟨haε.le.trans hr.1, hr.2.trans hmid.2⟩) x₀
  change rank (b - ε / 2) x₀ = 0 ∨ rank (b - ε / 2) x₀ = 1 ∨
    rank (b - ε / 2) x₀ = 3 at htri
  rwa [hleft _ hmid x₀] at htri

end DifferentialGeometry.PDE.RicciFlow
