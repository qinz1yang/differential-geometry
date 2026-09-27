import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakGradientSource
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakTimeDerivativeBound
import DifferentialGeometry.Analysis.Integration.Lp.Multiplication
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

variable {P ι : Type*} [MeasurableSpace P] [Fintype ι]
  {μ : Measure P}

private theorem norm_sum_mul_fields
    (a : ι → P → ℝ) (ha : ∀ i, MemLp (a i) ∞ μ)
    (C : ι → ℝ)
    (hbound : ∀ i, ∀ᵐ p ∂μ, ‖a i p‖ ≤ C i)
    (V : ι → P → ℝ) (hV : ∀ i, MemLp (V i) 2 μ) :
    ∃ F : Lp ℝ 2 μ,
      (F =ᵐ[μ] fun p => ∑ i, a i p * V i p) ∧
      ‖F‖ ≤ ∑ i, C i * ‖(hV i).toLp (V i)‖ := by
  have hmem (i) : MemLp (fun p => a i p * V i p) 2 μ :=
    (hV i).mul (r := 2) (ha i)
  let G : ι → Lp ℝ 2 μ := fun i => (hmem i).toLp (fun p => a i p * V i p)
  let F : Lp ℝ 2 μ := ∑ i, G i
  have hG (i) : G i =ᵐ[μ] fun p => a i p * V i p := (hmem i).coeFn_toLp
  have hF : F =ᵐ[μ] fun p => ∑ i, a i p * V i p := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ G, ae_all_iff.mpr (fun i => hG i)] with p hp h
    have hp' : F p = ∑ i, G i p := by simpa [F] using hp
    rw [hp']
    simp_rw [h]
  refine ⟨F, hF, ?_⟩
  apply norm_varying_coefficient_sum_le a ha C hbound (fun i => (hV i).toLp (V i)) F
  filter_upwards [hF, ae_all_iff.mpr (fun i => (hV i).coeFn_toLp)] with p hp hVp
  simpa only [hVp] using hp

private theorem exists_lp_gradient_source_bound
    (dA dDA : ι → ι → P → ℝ)
    (hdA : ∀ i j, MemLp (dA i j) ∞ μ)
    (hdDA : ∀ i j, MemLp (dDA i j) ∞ μ)
    (CA CDA : ι → ι → ℝ)
    (hbdA : ∀ i j, ∀ᵐ p ∂μ, ‖dA i j p‖ ≤ CA i j)
    (hbdDA : ∀ i j, ∀ᵐ p ∂μ, ‖dDA i j p‖ ≤ CDA i j)
    (dC C : ι → P → ℝ) (hdC : ∀ i, MemLp (dC i) ∞ μ)
    (hCmem : ∀ i, MemLp (C i) ∞ μ)
    (Cd CC : ι → ℝ)
    (hbdC : ∀ i, ∀ᵐ p ∂μ, ‖dC i p‖ ≤ Cd i)
    (hbdCC : ∀ i, ∀ᵐ p ∂μ, ‖C i p‖ ≤ CC i)
    (dC0 C0 dρ ddρ : P → ℝ)
    (hdC0 : MemLp dC0 ∞ μ) (hC0 : MemLp C0 ∞ μ)
    (hdρ : MemLp dρ ∞ μ) (hddρ : MemLp ddρ ∞ μ)
    (Cd0 C0b Cρ Cddρ : ℝ)
    (hbdC0 : ∀ᵐ p ∂μ, ‖dC0 p‖ ≤ Cd0)
    (hbC0 : ∀ᵐ p ∂μ, ‖C0 p‖ ≤ C0b)
    (hbdρ : ∀ᵐ p ∂μ, ‖dρ p‖ ≤ Cρ)
    (hbddρ : ∀ᵐ p ∂μ, ‖ddρ p‖ ≤ Cddρ)
    (H : ι → ι → P → ℝ) (hH : ∀ i j, MemLp (H i j) 2 μ)
    (V : ι → P → ℝ) (hV : ∀ i, MemLp (V i) 2 μ)
    (U R : P → ℝ) (hU : MemLp U 2 μ) (hR : MemLp R 2 μ)
    (k : ι) :
    ∃ F : Lp ℝ 2 μ,
      (F =ᵐ[μ] fun p =>
        (∑ i, ∑ j, dA i j p * H i j p) +
        (∑ i, ∑ j, dDA i j p * V i p) +
        (∑ i, C i p * H i k p) +
        (∑ i, dC i p * V i p) +
        C0 p * V k p + dC0 p * U p - dρ p * R p - ddρ p * U p) ∧
      ‖F‖ ≤
        (∑ i, ∑ j, CA i j * ‖(hH i j).toLp (H i j)‖) +
        (∑ i, ∑ j, CDA i j * ‖(hV i).toLp (V i)‖) +
        (∑ i, CC i * ‖(hH i k).toLp (H i k)‖) +
        (∑ i, Cd i * ‖(hV i).toLp (V i)‖) +
        C0b * ‖(hV k).toLp (V k)‖ + Cd0 * ‖hU.toLp U‖ +
        Cρ * ‖hR.toLp R‖ + Cddρ * ‖hU.toLp U‖ := by
  have h1 : ∃ f : Lp ℝ 2 μ,
      (f =ᵐ[μ] fun p => ∑ i, ∑ j, dA i j p * H i j p) ∧
      ‖f‖ ≤ ∑ i, ∑ j, CA i j * ‖(hH i j).toLp (H i j)‖ := by
    let a : (ι × ι) → P → ℝ := fun ij p => dA ij.1 ij.2 p
    let c : (ι × ι) → ℝ := fun ij => CA ij.1 ij.2
    let v : (ι × ι) → P → ℝ := fun ij p => H ij.1 ij.2 p
    have ha : ∀ ij, MemLp (a ij) ∞ μ := fun ij => hdA ij.1 ij.2
    have hb : ∀ ij, ∀ᵐ p ∂μ, ‖a ij p‖ ≤ c ij := fun ij => hbdA ij.1 ij.2
    have hv : ∀ ij, MemLp (v ij) 2 μ := fun ij => hH ij.1 ij.2
    obtain ⟨f, hf, hn⟩ := norm_sum_mul_fields a ha c hb v hv
    refine ⟨f, ?_, ?_⟩
    · filter_upwards [hf] with p hp
      simpa only [a, v, Fintype.sum_prod_type] using hp
    · simpa only [c, v, Fintype.sum_prod_type] using hn
  have h2 : ∃ f : Lp ℝ 2 μ,
      (f =ᵐ[μ] fun p => ∑ i, ∑ j, dDA i j p * V i p) ∧
      ‖f‖ ≤ ∑ i, ∑ j, CDA i j * ‖(hV i).toLp (V i)‖ := by
    let a : (ι × ι) → P → ℝ := fun ij p => dDA ij.1 ij.2 p
    let c : (ι × ι) → ℝ := fun ij => CDA ij.1 ij.2
    let v : (ι × ι) → P → ℝ := fun ij p => V ij.1 p
    have ha : ∀ ij, MemLp (a ij) ∞ μ := fun ij => hdDA ij.1 ij.2
    have hb : ∀ ij, ∀ᵐ p ∂μ, ‖a ij p‖ ≤ c ij := fun ij => hbdDA ij.1 ij.2
    have hv : ∀ ij, MemLp (v ij) 2 μ := fun ij => hV ij.1
    obtain ⟨f, hf, hn⟩ := norm_sum_mul_fields a ha c hb v hv
    refine ⟨f, ?_, ?_⟩
    · filter_upwards [hf] with p hp
      simpa only [a, v, Fintype.sum_prod_type] using hp
    · simpa only [c, v, Fintype.sum_prod_type] using hn
  have h3 : ∃ f : Lp ℝ 2 μ,
      (f =ᵐ[μ] fun p => ∑ i, C i p * H i k p) ∧
      ‖f‖ ≤ ∑ i, CC i * ‖(hH i k).toLp (H i k)‖ :=
    norm_sum_mul_fields C hCmem CC hbdCC (fun i p => H i k p) (fun i => hH i k)
  have h4 : ∃ f : Lp ℝ 2 μ,
      (f =ᵐ[μ] fun p => ∑ i, dC i p * V i p) ∧
      ‖f‖ ≤ ∑ i, Cd i * ‖(hV i).toLp (V i)‖ :=
    norm_sum_mul_fields dC hdC Cd hbdC V hV
  have h5 : ∃ f : Lp ℝ 2 μ,
      (f =ᵐ[μ] fun p => C0 p * V k p) ∧
      ‖f‖ ≤ C0b * ‖(hV k).toLp (V k)‖ := by
    obtain ⟨f, hf, hn⟩ := norm_sum_mul_fields (ι := Unit) (fun _ => C0) (fun _ => hC0)
      (fun _ => C0b) (fun _ => hbC0) (fun _ p => V k p) (fun _ => hV k)
    exact ⟨f, (by simpa using hf), (by simpa using hn)⟩
  have h6 : ∃ f : Lp ℝ 2 μ,
      (f =ᵐ[μ] fun p => dC0 p * U p) ∧ ‖f‖ ≤ Cd0 * ‖hU.toLp U‖ := by
    obtain ⟨f, hf, hn⟩ := norm_sum_mul_fields (ι := Unit) (fun _ => dC0) (fun _ => hdC0)
      (fun _ => Cd0) (fun _ => hbdC0) (fun _ p => U p) (fun _ => hU)
    exact ⟨f, (by simpa using hf), (by simpa using hn)⟩
  have h7 : ∃ f : Lp ℝ 2 μ,
      (f =ᵐ[μ] fun p => dρ p * R p) ∧ ‖f‖ ≤ Cρ * ‖hR.toLp R‖ := by
    obtain ⟨f, hf, hn⟩ := norm_sum_mul_fields (ι := Unit) (fun _ => dρ) (fun _ => hdρ)
      (fun _ => Cρ) (fun _ => hbdρ) (fun _ p => R p) (fun _ => hR)
    exact ⟨f, (by simpa using hf), (by simpa using hn)⟩
  have h8 : ∃ f : Lp ℝ 2 μ,
      (f =ᵐ[μ] fun p => ddρ p * U p) ∧ ‖f‖ ≤ Cddρ * ‖hU.toLp U‖ := by
    obtain ⟨f, hf, hn⟩ := norm_sum_mul_fields (ι := Unit) (fun _ => ddρ) (fun _ => hddρ)
      (fun _ => Cddρ) (fun _ => hbddρ) (fun _ p => U p) (fun _ => hU)
    exact ⟨f, (by simpa using hf), (by simpa using hn)⟩
  obtain ⟨f1, hf1, hn1⟩ := h1
  obtain ⟨f2, hf2, hn2⟩ := h2
  obtain ⟨f3, hf3, hn3⟩ := h3
  obtain ⟨f4, hf4, hn4⟩ := h4
  obtain ⟨f5, hf5, hn5⟩ := h5
  obtain ⟨f6, hf6, hn6⟩ := h6
  obtain ⟨f7, hf7, hn7⟩ := h7
  obtain ⟨f8, hf8, hn8⟩ := h8
  let F : Lp ℝ 2 μ := f1 + f2 + f3 + f4 + f5 + f6 - f7 - f8
  refine ⟨F, ?_, ?_⟩
  · have eF : F =ᵐ[μ] fun p => f1 p + f2 p + f3 p + f4 p + f5 p + f6 p - f7 p - f8 p := by
      filter_upwards [Lp.coeFn_sub (f1 + f2 + f3 + f4 + f5 + f6 - f7) f8,
        Lp.coeFn_sub (f1 + f2 + f3 + f4 + f5 + f6) f7,
        Lp.coeFn_add (f1 + f2 + f3 + f4 + f5) f6,
        Lp.coeFn_add (f1 + f2 + f3 + f4) f5,
        Lp.coeFn_add (f1 + f2 + f3) f4,
        Lp.coeFn_add (f1 + f2) f3,
        Lp.coeFn_add f1 f2] with p e8 e7 e6 e5 e4 e3 e12
      have e8' : (f1 + f2 + f3 + f4 + f5 + f6 - f7 - f8) p =
          (f1 + f2 + f3 + f4 + f5 + f6 - f7) p - f8 p := by
        simpa only [Pi.sub_apply] using e8
      have e7' : (f1 + f2 + f3 + f4 + f5 + f6 - f7) p =
          (f1 + f2 + f3 + f4 + f5 + f6) p - f7 p := by
        simpa only [Pi.sub_apply] using e7
      have e6' : (f1 + f2 + f3 + f4 + f5 + f6) p =
          (f1 + f2 + f3 + f4 + f5) p + f6 p := by
        simpa only [Pi.add_apply] using e6
      have e5' : (f1 + f2 + f3 + f4 + f5) p =
          (f1 + f2 + f3 + f4) p + f5 p := by
        simpa only [Pi.add_apply] using e5
      have e4' : (f1 + f2 + f3 + f4) p =
          (f1 + f2 + f3) p + f4 p := by
        simpa only [Pi.add_apply] using e4
      have e3' : (f1 + f2 + f3) p = (f1 + f2) p + f3 p := by
        simpa only [Pi.add_apply] using e3
      have e12' : (f1 + f2) p = f1 p + f2 p := by
        simpa only [Pi.add_apply] using e12
      calc
        F p = (f1 + f2 + f3 + f4 + f5 + f6 - f7 - f8) p := by rfl
        _ = (f1 + f2 + f3 + f4 + f5 + f6 - f7) p - f8 p := e8'
        _ = ((f1 + f2 + f3 + f4 + f5 + f6) p - f7 p) - f8 p := by rw [e7']
        _ = (((f1 + f2 + f3 + f4 + f5) p + f6 p) - f7 p) - f8 p := by rw [e6']
        _ = ((((f1 + f2 + f3 + f4) p + f5 p) + f6 p) - f7 p) - f8 p := by rw [e5']
        _ = (((((f1 + f2 + f3) p + f4 p) + f5 p) + f6 p) - f7 p) - f8 p := by rw [e4']
        _ = ((((((f1 + f2) p + f3 p) + f4 p) + f5 p) + f6 p) - f7 p) - f8 p := by rw [e3']
        _ = ((((((f1 p + f2 p) + f3 p) + f4 p) + f5 p) + f6 p) - f7 p) - f8 p := by rw [e12']
    filter_upwards [eF, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8] with p hp h1 h2 h3 h4 h5 h6 h7 h8
    rw [hp, h1, h2, h3, h4, h5, h6, h7, h8]
  · calc
      ‖F‖ ≤ ‖f1‖ + ‖f2‖ + ‖f3‖ + ‖f4‖ + ‖f5‖ + ‖f6‖ + ‖f7‖ + ‖f8‖ := by
        dsimp only [F]
        linarith [norm_sub_le (f1 + f2 + f3 + f4 + f5 + f6 - f7) f8,
          norm_sub_le (f1 + f2 + f3 + f4 + f5 + f6) f7,
          norm_add_le f1 f2, norm_add_le (f1 + f2) f3,
          norm_add_le (f1 + f2 + f3) f4, norm_add_le (f1 + f2 + f3 + f4) f5,
          norm_add_le (f1 + f2 + f3 + f4 + f5) f6]
      _ ≤ _ := by gcongr

private theorem norm_gradient_source_le
    (dA dDA : ι → ι → P → ℝ)
    (hdA : ∀ i j, MemLp (dA i j) ∞ μ)
    (hdDA : ∀ i j, MemLp (dDA i j) ∞ μ)
    (CA CDA : ι → ι → ℝ)
    (hbdA : ∀ i j, ∀ᵐ p ∂μ, ‖dA i j p‖ ≤ CA i j)
    (hbdDA : ∀ i j, ∀ᵐ p ∂μ, ‖dDA i j p‖ ≤ CDA i j)
    (dC C : ι → P → ℝ) (hdC : ∀ i, MemLp (dC i) ∞ μ)
    (hCmem : ∀ i, MemLp (C i) ∞ μ)
    (Cd CC : ι → ℝ)
    (hbdC : ∀ i, ∀ᵐ p ∂μ, ‖dC i p‖ ≤ Cd i)
    (hbdCC : ∀ i, ∀ᵐ p ∂μ, ‖C i p‖ ≤ CC i)
    (dC0 C0 dρ ddρ : P → ℝ)
    (hdC0 : MemLp dC0 ∞ μ) (hC0 : MemLp C0 ∞ μ)
    (hdρ : MemLp dρ ∞ μ) (hddρ : MemLp ddρ ∞ μ)
    (Cd0 C0b Cρ Cddρ : ℝ)
    (hbdC0 : ∀ᵐ p ∂μ, ‖dC0 p‖ ≤ Cd0)
    (hbC0 : ∀ᵐ p ∂μ, ‖C0 p‖ ≤ C0b)
    (hbdρ : ∀ᵐ p ∂μ, ‖dρ p‖ ≤ Cρ)
    (hbddρ : ∀ᵐ p ∂μ, ‖ddρ p‖ ≤ Cddρ)
    (H : ι → ι → P → ℝ) (hH : ∀ i j, MemLp (H i j) 2 μ)
    (V : ι → P → ℝ) (hV : ∀ i, MemLp (V i) 2 μ)
    (U R : P → ℝ) (hU : MemLp U 2 μ) (hR : MemLp R 2 μ)
    (k : ι) (F : Lp ℝ 2 μ)
    (hF : F =ᵐ[μ] fun p =>
        (∑ i, ∑ j, dA i j p * H i j p) +
        (∑ i, ∑ j, dDA i j p * V i p) +
        (∑ i, C i p * H i k p) +
        (∑ i, dC i p * V i p) +
        C0 p * V k p + dC0 p * U p - dρ p * R p - ddρ p * U p) :
      ‖F‖ ≤
        (∑ i, ∑ j, CA i j * ‖(hH i j).toLp (H i j)‖) +
        (∑ i, ∑ j, CDA i j * ‖(hV i).toLp (V i)‖) +
        (∑ i, CC i * ‖(hH i k).toLp (H i k)‖) +
        (∑ i, Cd i * ‖(hV i).toLp (V i)‖) +
        C0b * ‖(hV k).toLp (V k)‖ + Cd0 * ‖hU.toLp U‖ +
        Cρ * ‖hR.toLp R‖ + Cddρ * ‖hU.toLp U‖ := by
  obtain ⟨F', hF', hnorm⟩ := exists_lp_gradient_source_bound dA dDA hdA hdDA CA CDA hbdA hbdDA
    dC C hdC hCmem Cd CC hbdC hbdCC dC0 C0 dρ ddρ hdC0 hC0 hdρ hddρ
    Cd0 C0b Cρ Cddρ hbdC0 hbC0 hbdρ hbddρ H hH V hV U R hU hR k
  have heq : F = F' := Lp.ext (hF.trans hF'.symm)
  rwa [heq]

open Bundle Manifold Set
open scoped ContDiff Manifold NNReal Topology
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))


theorem IsWeakEvolutionSolution.exists_lp_weak_gradient_equation_source_norm_le
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let B := fun i (p : ℝ × EuStd) =>
      DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i
        ((toEuclidean (E := EuN)).symm p.2)
    let τ := fun (p : ℝ × EuStd) => traceTimeDerivMetric (I := I_hs) G.metric p.1
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
    let C := fun i (p : ℝ × EuStd) => ρ p * B i p
    let C₀ := fun (p : ℝ × EuStd) => ρ p * ((1 / 2 : ℝ) * τ p - a p.1)
    let DA := fun k i j (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single k 1)
    let DDA := fun k i j (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => DA k i j (p.1, z)) p.2 (EuclideanSpace.single j 1)
    let DC := fun k i (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => C i (p.1, z)) p.2 (EuclideanSpace.single k 1)
    let DC₀ := fun k (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => C₀ (p.1, z)) p.2 (EuclideanSpace.single k 1)
    let Dρ := fun k (p : ℝ × EuStd) => fderiv ℝ ρ p (0, EuclideanSpace.single k 1)
    let DDρ := fun k (p : ℝ × EuStd) => fderiv ℝ (Dρ k) p (1, 0)
    ∃ R : Lp ℝ 2 ν, ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ F : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t,z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      (∀ k, (F k =ᵐ[ν] fun p =>
        (∑ i, ∑ j,
          (fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single k 1) * H i j p +
            fderiv ℝ (fun z => fderiv ℝ (fun y => A i j (p.1, y)) z
              (EuclideanSpace.single k 1)) p.2 (EuclideanSpace.single j 1) * V i p)) +
          (∑ i, (fderiv ℝ (fun z => C i (p.1, z)) p.2 (EuclideanSpace.single k 1) * V i p +
            C i p * H i k p)) +
          (fderiv ℝ (fun z => C₀ (p.1, z)) p.2 (EuclideanSpace.single k 1) -
            fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single k 1)) p (1, 0)) * U p +
          C₀ p * V k p - fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p)) ∧
      (∀ k, ‖F k‖ ≤
        (∑ i, ∑ j, lpNorm (DA k i j) ∞ ν * ‖H i j‖) +
        (∑ i, ∑ j, lpNorm (DDA k i j) ∞ ν * lpNorm (V i) 2 ν) +
        (∑ i, lpNorm (C i) ∞ ν * ‖H i k‖) +
        (∑ i, lpNorm (DC k i) ∞ ν * lpNorm (V i) 2 ν) +
        lpNorm C₀ ∞ ν * lpNorm (V k) 2 ν + lpNorm (DC₀ k) ∞ ν * lpNorm U 2 ν +
        lpNorm (Dρ k) ∞ ν * ‖R‖ + lpNorm (DDρ k) ∞ ν * lpNorm U 2 ν) ∧
      ∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F k p * φ p ∂ν := by
  intro μ ν ρ A U V B τ C C₀ DA DDA DC DC₀ Dρ DDρ
  classical
  obtain ⟨R, H, F, hR, hH, hHsym, hFormula, hF⟩ :=
    hu.exists_lp_weak_gradient_equation_with_source_formula hXcont hacont α hΩ hΩc hΩs
      hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  refine ⟨R, H, F, hR, hH, hHsym, hFormula, ?_, hF⟩
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  intro k
  have hΩ₀s := hΩ₀Ω.trans (subset_closure.trans hΩs)
  have hρ : MemLp ρ ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.densityOnEuclid_family_memLp_top hG isCompact_Icc hreg α
      hΩ₀.measurableSet hΩ₀c (hΩ₀s.trans (image_mono interior_subset)) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hB (i) : MemLp (B i) ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_family_memLp_top X isCompact_Icc
      measurableSet_Icc α (hXcont.mono (prod_mono Subset.rfl (subset_univ _)))
      hΩ₀.measurableSet hΩ₀c (hΩ₀s.trans (image_mono interior_subset)) i (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hτ : MemLp τ ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.traceTimeDerivMetric_comp_chartInverse_memLp_top hG isCompact_Icc
      hreg α hΩ₀.measurableSet hΩ₀c (hΩ₀s.trans (image_mono interior_subset)) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have ha : MemLp (fun p : ℝ × EuStd => a p.1) ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hc := hacont.comp continuousOn_fst (fun _ hp => hp.1 : MapsTo Prod.fst
      (Icc (0 : ℝ) T ×ˢ closure Ω₀) (Icc (0 : ℝ) T))
    have hb := hc.memLp_top_of_subset_isCompact (isCompact_Icc.prod hΩ₀c)
      (measurableSet_Icc.prod hΩ₀.measurableSet) (prod_mono Subset.rfl subset_closure)
      (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hC (i) : MemLp (C i) ∞ (μ.prod (volume.restrict Ω₀)) := (hB i).mul hρ
  have hC₀ : MemLp C₀ ∞ (μ.prod (volume.restrict Ω₀)) := ((hτ.const_mul (1 / 2 : ℝ)).sub ha).mul hρ
  have hDCmem (i) : MemLp (fun p => fderiv ℝ (fun x => C i (p.1, x)) p.2 (EuclideanSpace.single k 1))
      ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.densityOnEuclid_mul_chartCoeffOnE_family_fderiv_memLp_top hG isCompact_Icc
      hreg α X hXsmooth hΩ₀.measurableSet hΩ₀c hΩ₀s i (EuclideanSpace.single k 1) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hDC₀mem : MemLp (fun p => fderiv ℝ (fun x => C₀ (p.1, x)) p.2 (EuclideanSpace.single k 1))
      ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.potentialCoefficient_family_fderiv_memLp_top hG isCompact_Icc
      hreg α hΩ₀.measurableSet hΩ₀c hΩ₀s hacont (EuclideanSpace.single k 1) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hDA (i j) : MemLp (DA k i j) ∞ ν := by
    have hb := MetricExtension.weightedInvGramOnEuclid_family_fderiv_memLp_top hG isCompact_Icc hreg α
      hΩ₀.measurableSet hΩ₀c (hΩ₀Ω.trans (subset_closure.trans hΩs)) i j k (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hDDA (i j) : MemLp
      (fun p => fderiv ℝ (fun x => DA k i j (p.1, x)) p.2 (EuclideanSpace.single j 1)) ∞ ν := by
    have hb := MetricExtension.weightedInvGramOnEuclid_family_fderiv_fderiv_memLp_top hG isCompact_Icc
      hreg α hΩ₀.measurableSet hΩ₀c (hΩ₀Ω.trans (subset_closure.trans hΩs)) i j
      (EuclideanSpace.single k 1) (EuclideanSpace.single j 1) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hρall : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ Ω) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (Set.prod_mono Subset.rfl (subset_closure.trans (hΩs.trans (image_mono interior_subset))))
  have hlift (f : ℝ × EuStd → ℝ) (hc : ContinuousOn f (D.regular ×ˢ Ω)) : MemLp f ∞ ν := by
    have hb := (hc.mono (prod_mono hreg hΩ₀Ω)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩ₀c) (measurableSet_Icc.prod hΩ₀.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hDρc : ContDiffOn ℝ (⊤ : ℕ∞) (Dρ k) (D.regular ×ˢ Ω) :=
    (hρall.fderiv_of_isOpen (D.regular_isOpen.prod hΩ) (by simp)).clm_apply contDiffOn_const
  have hDDρc : ContDiffOn ℝ (⊤ : ℕ∞) (DDρ k) (D.regular ×ˢ Ω) :=
    (hDρc.fderiv_of_isOpen (D.regular_isOpen.prod hΩ) (by simp)).clm_apply contDiffOn_const
  have hDρ := hlift _ hDρc.continuousOn
  have hDDρ := hlift _ hDDρc.continuousOn
  have he : F k =ᵐ[ν] fun p =>
      (∑ i, ∑ j, DA k i j p * H i j p) +
      (∑ i, ∑ j, DDA k i j p * V i p) +
      (∑ i, C i p * H i k p) + (∑ i, DC k i p * V i p) +
      C₀ p * V k p + DC₀ k p * U p - Dρ k p * R p - DDρ k p * U p := by
    filter_upwards [hFormula k] with p hp
    rw [hp]
    simp only [DA, DDA, DC, DC₀, Dρ, DDρ, Finset.sum_add_distrib]
    ring
  have hb := norm_gradient_source_le (DA k) (DDA k) hDA hDDA
    (fun i j => lpNorm (DA k i j) ∞ ν) (fun i j => lpNorm (DDA k i j) ∞ ν)
    (fun i j => ae_le_lpNorm_exponent_top (hDA i j))
    (fun i j => ae_le_lpNorm_exponent_top (hDDA i j))
    (DC k) C hDCmem hC (fun i => lpNorm (DC k i) ∞ ν) (fun i => lpNorm (C i) ∞ ν)
    (fun i => ae_le_lpNorm_exponent_top (hDCmem i)) (fun i => ae_le_lpNorm_exponent_top (hC i))
    (DC₀ k) C₀ (Dρ k) (DDρ k) hDC₀mem hC₀ hDρ hDDρ
    (lpNorm (DC₀ k) ∞ ν) (lpNorm C₀ ∞ ν) (lpNorm (Dρ k) ∞ ν) (lpNorm (DDρ k) ∞ ν)
    (ae_le_lpNorm_exponent_top hDC₀mem) (ae_le_lpNorm_exponent_top hC₀)
    (ae_le_lpNorm_exponent_top hDρ) (ae_le_lpNorm_exponent_top hDDρ)
    (fun i j p => H i j p) (fun i j => Lp.memLp (H i j)) (fun i p => V i p) hV U R hU (Lp.memLp R) k (F k) he
  simpa only [Lp.toLp_coeFn, Lp.norm_toLp,
    toReal_eLpNorm (hV _).aestronglyMeasurable, toReal_eLpNorm hU.aestronglyMeasurable] using hb

theorem IsWeakEvolutionSolution.exists_lp_weak_gradient_equation_source_bound
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let B := fun i (p : ℝ × EuStd) =>
      DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i
        ((toEuclidean (E := EuN)).symm p.2)
    let τ := fun (p : ℝ × EuStd) => traceTimeDerivMetric (I := I_hs) G.metric p.1
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
    let C := fun i (p : ℝ × EuStd) => ρ p * B i p
    let C₀ := fun (p : ℝ × EuStd) => ρ p * ((1 / 2 : ℝ) * τ p - a p.1)
    let DA := fun k i j (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single k 1)
    let DDA := fun k i j (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => DA k i j (p.1, z)) p.2 (EuclideanSpace.single j 1)
    let DC := fun k i (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => C i (p.1, z)) p.2 (EuclideanSpace.single k 1)
    let DC₀ := fun k (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => C₀ (p.1, z)) p.2 (EuclideanSpace.single k 1)
    let Dρ := fun k (p : ℝ × EuStd) => fderiv ℝ ρ p (0, EuclideanSpace.single k 1)
    let DDρ := fun k (p : ℝ × EuStd) => fderiv ℝ (Dρ k) p (1, 0)
    let KR := fun (H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν) =>
      (∑ i, ∑ j, lpNorm (fun p => (ρ p)⁻¹ * A i j p) ∞ ν * ‖H i j‖) +
      (∑ i, ∑ j, lpNorm (fun p => (ρ p)⁻¹ * DA j i j p) ∞ ν * lpNorm (V i) 2 ν) +
      (∑ i, lpNorm (fun p => (ρ p)⁻¹ * C i p) ∞ ν * lpNorm (V i) 2 ν) +
      lpNorm (fun p => (ρ p)⁻¹ * (C₀ p - fderiv ℝ ρ p (1, 0))) ∞ ν * lpNorm U 2 ν
    ∃ R : Lp ℝ 2 ν, ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ F : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t,z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      (∀ k, (F k =ᵐ[ν] fun p =>
        (∑ i, ∑ j,
          (fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single k 1) * H i j p +
            fderiv ℝ (fun z => fderiv ℝ (fun y => A i j (p.1, y)) z
              (EuclideanSpace.single k 1)) p.2 (EuclideanSpace.single j 1) * V i p)) +
          (∑ i, (fderiv ℝ (fun z => C i (p.1, z)) p.2 (EuclideanSpace.single k 1) * V i p +
            C i p * H i k p)) +
          (fderiv ℝ (fun z => C₀ (p.1, z)) p.2 (EuclideanSpace.single k 1) -
            fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single k 1)) p (1, 0)) * U p +
          C₀ p * V k p - fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p)) ∧
      ‖R‖ ≤ KR H ∧
      (∀ k, ‖F k‖ ≤
        (∑ i, ∑ j, lpNorm (DA k i j) ∞ ν * ‖H i j‖) +
        (∑ i, ∑ j, lpNorm (DDA k i j) ∞ ν * lpNorm (V i) 2 ν) +
        (∑ i, lpNorm (C i) ∞ ν * ‖H i k‖) +
        (∑ i, lpNorm (DC k i) ∞ ν * lpNorm (V i) 2 ν) +
        lpNorm C₀ ∞ ν * lpNorm (V k) 2 ν + lpNorm (DC₀ k) ∞ ν * lpNorm U 2 ν +
        lpNorm (Dρ k) ∞ ν * KR H + lpNorm (DDρ k) ∞ ν * lpNorm U 2 ν) ∧
      ∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F k p * φ p ∂ν := by
  intro μ ν ρ A U V B τ C C₀ DA DDA DC DC₀ Dρ DDρ KR
  obtain ⟨R, H, F, hR, hH, hHsym, hFormula, hsource, hF⟩ :=
    hu.exists_lp_weak_gradient_equation_source_norm_le hXcont hacont α hΩ hΩc hΩs
      hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  have hRnorm : ‖R‖ ≤ KR H := hu.norm_weak_time_derivative_le hXcont hacont α hΩ hΩc hΩs
    hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω H hH R hR
  refine ⟨R, H, F, hR, hH, hHsym, hFormula, hRnorm, ?_, hF⟩
  intro k
  apply (hsource k).trans
  gcongr
  exact lpNorm_nonneg

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
