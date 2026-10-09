import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.FirstContact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ScalarDerivativeContactTime

noncomputable section
open Set
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
universe u

theorem IncomingSlab.exists_closedPrefix_first_scalar_derivative_contact
    {P : OrientedThreeStage.{u}} {start finish : ℝ} (G : P.IncomingSlab start finish)
    {a b C q Q : ℝ} (hstart : start < a) (hab : a ≤ b) (hfinish : b < finish)
    (hC : 0 < C) (hq : 0 < q) (hqQ : q ≤ Q)
    (hinitial : ∀ x : P.Carrier,
      (G.flow.base.metric a).inner x (gradientFun (G.flow.base.metric a) (G.flow.scalar a) x)
        (gradientFun (G.flow.base.metric a) (G.flow.scalar a) x) < C ^ 2 * (max q (G.flow.scalar a x)) ^ 3 ∧
      |derivWithin (fun t => G.flow.scalar t x) (Iic a) a| < C * (max q (G.flow.scalar a x)) ^ 2)
    (hlow : ∀ t ∈ Icc a b, ∀ x : P.Carrier, G.flow.scalar t x ≤ Q →
      (G.flow.base.metric t).inner x (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x)
        (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x) < C ^ 2 * (max q (G.flow.scalar t x)) ^ 3 ∧
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| < C * (max q (G.flow.scalar t x)) ^ 2)
    (hpast : ∀ t ∈ Ioo start a, ∀ y : P.Carrier, q ≤ G.flow.scalar t y →
      (G.flow.base.metric t).inner y (gradientFun (G.flow.base.metric t) (G.flow.scalar t) y)
        (gradientFun (G.flow.base.metric t) (G.flow.scalar t) y) < C ^ 2 * G.flow.scalar t y ^ 3 ∧
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| < C * G.flow.scalar t y ^ 2)
    (hfail : ∃ x : P.Carrier,
      C ^ 2 * (max q (G.flow.scalar b x)) ^ 3 ≤
        (G.flow.base.metric b).inner x (gradientFun (G.flow.base.metric b) (G.flow.scalar b) x)
          (gradientFun (G.flow.base.metric b) (G.flow.scalar b) x) ∨
      C * (max q (G.flow.scalar b x)) ^ 2 ≤ |derivWithin (fun t => G.flow.scalar t x) (Iic b) b|) :
    ∃ (τ : ℝ) (hτ : τ ∈ Ioc a b),
      let S := G.closedPrefix τ (hstart.trans hτ.1) (hτ.2.trans_lt hfinish);
      ∃ x : P.Carrier, Q < S.flow.scalar τ x ∧
      ((∃ v : TangentSpace ThreeModel x, v ≠ 0 ∧
        C * S.flow.scalar τ x * Real.sqrt (S.flow.scalar τ x) *
            Real.sqrt ((S.flow.base.metric τ).inner x v v) =
          |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (S.flow.scalar τ) x v)|) ∨
        |derivWithin (fun t => S.flow.scalar t x) (Iic τ) τ| = C * S.flow.scalar τ x ^ 2) ∧
      (∀ t ∈ Ico a τ, ∀ y : P.Carrier, q ≤ S.flow.scalar t y →
        (S.flow.base.metric t).inner y (gradientFun (S.flow.base.metric t) (S.flow.scalar t) y)
          (gradientFun (S.flow.base.metric t) (S.flow.scalar t) y) < C ^ 2 * S.flow.scalar t y ^ 3 ∧
        (∀ v : TangentSpace ThreeModel y, |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (S.flow.scalar t) y v)| ≤
          C * S.flow.scalar t y * Real.sqrt (S.flow.scalar t y) *
            Real.sqrt ((S.flow.base.metric t).inner y v v)) ∧
        |derivWithin (fun v => S.flow.scalar v y) (Iic t) t| < C * S.flow.scalar t y ^ 2) ∧
      (∀ t ∈ Ioo start τ, ∀ y : P.Carrier, q ≤ S.flow.scalar t y →
        (S.flow.base.metric t).inner y (gradientFun (S.flow.base.metric t) (S.flow.scalar t) y)
          (gradientFun (S.flow.base.metric t) (S.flow.scalar t) y) < C ^ 2 * S.flow.scalar t y ^ 3 ∧
        |derivWithin (fun v => S.flow.scalar v y) (Iic t) t| < C * S.flow.scalar t y ^ 2) ∧
      (∀ y : P.Carrier, q ≤ S.flow.scalar τ y →
        (∀ v : TangentSpace ThreeModel y, |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (S.flow.scalar τ) y v)| ≤
          C * S.flow.scalar τ y * Real.sqrt (S.flow.scalar τ y) *
            Real.sqrt ((S.flow.base.metric τ).inner y v v)) ∧
        |derivWithin (fun v => S.flow.scalar v y) (Iic τ) τ| ≤ C * S.flow.scalar τ y ^ 2) := by
  have hinterval : Icc a b ⊆ Ioo start finish := fun t ht =>
    ⟨hstart.trans_le ht.1, ht.2.trans_lt hfinish⟩
  obtain ⟨τ, hτ, x, hhigh, hcontact, hbefore, hat⟩ :=
    G.flow.exists_first_scalar_derivative_contact_above_scalar_bound G.equation hab hinterval
      hC hq hqQ hinitial hlow hfail
  refine ⟨τ, hτ, x, hhigh, hcontact, hbefore, ?_, hat⟩
  intro t ht y hy
  by_cases hta : t < a
  · exact hpast t ⟨ht.1, hta⟩ y hy
  · have hb := hbefore t ⟨le_of_not_gt hta, ht.2⟩ y hy
    exact ⟨hb.1, hb.2.2⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Filter
open scoped _root_.Topology

universe v

theorem exists_scalar_derivative_contact_sequence_of_failures
    (P : OrientedThreeStage.{v}) (g : P.Metric) (Dbig : ℝ) (m : ℕ) {C q amin δ₀ : ℝ}
    (hC : 0 < C) (hq : 0 < q) (hamin : 0 < amin)
    (hcounter : ∀ Q : ℝ, q ≤ Q → ∀ ε : ℝ, 0 < ε →
      ∃ (H : RetainedCoreHistory.{v}) (_ : InitialIdentification P g H.toHistory)
        (parameters : CutoffParameters)
        (records : ∀ j, GeometricCutoffRecord H.toHistory j parameters)
        (finish : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
          (H.time (Fin.last H.eventCount)) finish) (a b : ℝ),
        G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount) ∧
        H.time (Fin.last H.eventCount) < a ∧ a ≤ b ∧ b < finish ∧ amin ≤ a ∧
        parameters.modelRadius = Dbig ∧ m ≤ parameters.modelOrder ∧
        (∀ j boundary, ((records j).static boundary).hasCanonicalWindow) ∧
        parameters.modelAccuracy ≤ ε ∧
        (∀ j boundary, (records j).delta boundary ≤ δ₀) ∧
        (∀ j, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          ∀ y : (H.stage j.castSucc).Carrier, q < (H.toHistory.event j).incoming.flow.scalar t y →
          |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) ∧
        (∀ x,
          (G.flow.base.metric a).inner x (gradientFun (G.flow.base.metric a) (G.flow.scalar a) x)
            (gradientFun (G.flow.base.metric a) (G.flow.scalar a) x) < C ^ 2 * (max q (G.flow.scalar a x)) ^ 3 ∧
          |derivWithin (fun t => G.flow.scalar t x) (Iic a) a| < C * (max q (G.flow.scalar a x)) ^ 2) ∧
        (∀ t ∈ Icc a b, ∀ x, G.flow.scalar t x ≤ Q →
          (G.flow.base.metric t).inner x (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x)
            (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x) < C ^ 2 * (max q (G.flow.scalar t x)) ^ 3 ∧
          |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| < C * (max q (G.flow.scalar t x)) ^ 2) ∧
        (∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) a, ∀ y, q ≤ G.flow.scalar t y →
          (G.flow.base.metric t).inner y (gradientFun (G.flow.base.metric t) (G.flow.scalar t) y)
            (gradientFun (G.flow.base.metric t) (G.flow.scalar t) y) < C ^ 2 * G.flow.scalar t y ^ 3 ∧
          |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| < C * G.flow.scalar t y ^ 2) ∧
        (∃ x,
          C ^ 2 * (max q (G.flow.scalar b x)) ^ 3 ≤
            (G.flow.base.metric b).inner x (gradientFun (G.flow.base.metric b) (G.flow.scalar b) x)
              (gradientFun (G.flow.base.metric b) (G.flow.scalar b) x) ∨
          C * (max q (G.flow.scalar b x)) ^ 2 ≤ |derivWithin (fun t => G.flow.scalar t x) (Iic b) b|)) :
    ∃ (H : ℕ → RetainedCoreHistory.{v}) (_ : ∀ i, InitialIdentification P g (H i).toHistory)
      (parameters : ℕ → CutoffParameters)
      (records : ∀ i j, GeometricCutoffRecord (H i).toHistory j (parameters i))
      (finish : ℕ → ℝ)
      (G : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).IncomingSlab
        ((H i).time (Fin.last (H i).eventCount)) (finish i)) (a b : ℕ → ℝ)
      (hstart : ∀ i, (H i).time (Fin.last (H i).eventCount) < a i)
      (hfinish : ∀ i, b i < finish i) (τ : ℕ → ℝ) (hτ : ∀ i, τ i ∈ Ioc (a i) (b i)),
      let A := fun i => (G i).closedPrefix (τ i) ((hstart i).trans (hτ i).1)
        ((hτ i).2.trans_lt (hfinish i));
      ∃ x : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).Carrier,
        (∀ i, (G i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
          (H i).initialMetric (Fin.last (H i).eventCount)) ∧
        (∀ i, 0 < τ i ∧ amin ≤ τ i) ∧
        (∀ i, (parameters i).modelRadius = Dbig) ∧
        (∀ i, m ≤ (parameters i).modelOrder) ∧
        (∀ i j boundary, ((records i j).static boundary).hasCanonicalWindow) ∧
        (∀ i j boundary, (records i j).delta boundary ≤ δ₀) ∧
        (∀ i j, ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
          ∀ y : ((H i).stage j.castSucc).Carrier,
          q < ((H i).toHistory.event j).incoming.flow.scalar t y →
          |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2) ∧
        Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) ∧
        Tendsto (fun i => (A i).flow.scalar (τ i) (x i)) atTop atTop ∧
        (∀ i : ℕ, q + (i : ℝ) + 1 < (A i).flow.scalar (τ i) (x i) ∧
          ((∃ v : TangentSpace ThreeModel (x i), v ≠ 0 ∧
            C * (A i).flow.scalar (τ i) (x i) * Real.sqrt ((A i).flow.scalar (τ i) (x i)) *
                Real.sqrt (((A i).flow.base.metric (τ i)).inner (x i) v v) =
              |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (τ i)) (x i) v)|) ∨
            |derivWithin (fun t => (A i).flow.scalar t (x i)) (Iic (τ i)) (τ i)| =
              C * (A i).flow.scalar (τ i) (x i) ^ 2) ∧
          (∀ t ∈ Ico (a i) (τ i), ∀ y, q ≤ (A i).flow.scalar t y →
            ((A i).flow.base.metric t).inner y
              (gradientFun ((A i).flow.base.metric t) ((A i).flow.scalar t) y)
              (gradientFun ((A i).flow.base.metric t) ((A i).flow.scalar t) y) <
                C ^ 2 * (A i).flow.scalar t y ^ 3 ∧
            (∀ v : TangentSpace ThreeModel y,
              |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar t) y v)| ≤
                C * (A i).flow.scalar t y * Real.sqrt ((A i).flow.scalar t y) *
                  Real.sqrt (((A i).flow.base.metric t).inner y v v)) ∧
            |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| <
              C * (A i).flow.scalar t y ^ 2) ∧
          (∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (τ i), ∀ y,
            q ≤ (A i).flow.scalar t y →
            ((A i).flow.base.metric t).inner y
              (gradientFun ((A i).flow.base.metric t) ((A i).flow.scalar t) y)
              (gradientFun ((A i).flow.base.metric t) ((A i).flow.scalar t) y) <
                C ^ 2 * (A i).flow.scalar t y ^ 3 ∧
            |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| <
              C * (A i).flow.scalar t y ^ 2) ∧
          (∀ y, q ≤ (A i).flow.scalar (τ i) y →
            (∀ v : TangentSpace ThreeModel y,
              |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (τ i)) y v)| ≤
                C * (A i).flow.scalar (τ i) y * Real.sqrt ((A i).flow.scalar (τ i) y) *
                  Real.sqrt (((A i).flow.base.metric (τ i)).inner y v v)) ∧
            |derivWithin (fun v => (A i).flow.scalar v y) (Iic (τ i)) (τ i)| ≤
              C * (A i).flow.scalar (τ i) y ^ 2)) := by
  classical
  have hchoice (i : ℕ) := hcounter (q + (i : ℝ) + 1)
    (by have hi := Nat.cast_nonneg (α := ℝ) i; linarith)
    (1 / ((i : ℝ) + 1)) (by positivity)
  choose H identification parameters records finish G a b hinit hstart hab hfinish hminimum
    hmodelradius hmodelorder hwindows haccuracy hdelta hold hinitial hlow hpast hfail using hchoice
  have hcontact (i : ℕ) := (G i).exists_closedPrefix_first_scalar_derivative_contact
    (hstart i) (hab i) (hfinish i) hC hq
    (show q ≤ q + (i : ℝ) + 1 by have hi := Nat.cast_nonneg (α := ℝ) i; linarith)
    (hinitial i) (hlow i) (hpast i) (hfail i)
  choose τ hτ x hhigh hcontact hbefore hpast hat using hcontact
  refine ⟨H, identification, parameters, records, finish, G, a, b, hstart, hfinish, τ, hτ,
    x, hinit, ?_, hmodelradius, hmodelorder, hwindows, hdelta, hold, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hamin.trans_le ((hminimum i).trans (hτ i).1.le),
      (hminimum i).trans (hτ i).1.le⟩
  · exact squeeze_zero (fun i => (parameters i).modelAccuracy_pos.le) haccuracy
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · have hQ : Tendsto (fun i : ℕ => q + (i : ℝ) + 1) atTop atTop := by
      have hnat := tendsto_atTop_add_const_right atTop (q + 1)
        (tendsto_natCast_atTop_atTop (R := ℝ))
      convert hnat using 1
      ext i
      ring
    exact tendsto_atTop_mono (fun i => (hhigh i).le) hQ
  · exact fun i => ⟨hhigh i, hcontact i, hbefore i, hpast i, hat i⟩

theorem exists_scalar_derivative_contact_sequence_of_bounded_failures
    (P : OrientedThreeStage.{v}) (g : P.Metric) (Dbig : ℝ) (m : ℕ) (B δ₀ : ℝ) :
    ∃ amin : ℝ, 0 < amin ∧ ∀ C : ℝ, 0 < C → ∃ q : ℝ, 0 < q ∧
    ((∀ Q : ℝ, q ≤ Q → ∀ ε : ℝ, 0 < ε →
      ∃ (H : RetainedCoreHistory.{v}) (_ : InitialIdentification P g H.toHistory)
        (parameters : CutoffParameters)
        (records : ∀ j, GeometricCutoffRecord H.toHistory j parameters)
        (finish : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
          (H.time (Fin.last H.eventCount)) finish) (a b : ℝ),
        G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount) ∧
        H.time (Fin.last H.eventCount) = H.horizon ∧ finish ≤ B ∧
        H.time (Fin.last H.eventCount) < a ∧ a ≤ b ∧ b < finish ∧
        parameters.modelRadius = Dbig ∧ m ≤ parameters.modelOrder ∧
        (∀ j boundary, ((records j).static boundary).hasCanonicalWindow) ∧
        parameters.modelAccuracy ≤ ε ∧
        (∀ j boundary, (records j).delta boundary ≤ δ₀) ∧
        (∀ j, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          ∀ y : (H.stage j.castSucc).Carrier, q < (H.toHistory.event j).incoming.flow.scalar t y →
          |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) ∧
        (∀ x,
          (G.flow.base.metric a).inner x (gradientFun (G.flow.base.metric a) (G.flow.scalar a) x)
            (gradientFun (G.flow.base.metric a) (G.flow.scalar a) x) < C ^ 2 * (max q (G.flow.scalar a x)) ^ 3 ∧
          |derivWithin (fun t => G.flow.scalar t x) (Iic a) a| < C * (max q (G.flow.scalar a x)) ^ 2) ∧
        (∀ t ∈ Icc a b, ∀ x, G.flow.scalar t x ≤ Q →
          (G.flow.base.metric t).inner x (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x)
            (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x) < C ^ 2 * (max q (G.flow.scalar t x)) ^ 3 ∧
          |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| < C * (max q (G.flow.scalar t x)) ^ 2) ∧
        (∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) a, ∀ y, q ≤ G.flow.scalar t y →
          (G.flow.base.metric t).inner y (gradientFun (G.flow.base.metric t) (G.flow.scalar t) y)
            (gradientFun (G.flow.base.metric t) (G.flow.scalar t) y) < C ^ 2 * G.flow.scalar t y ^ 3 ∧
          |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| < C * G.flow.scalar t y ^ 2) ∧
        (∃ x,
          C ^ 2 * (max q (G.flow.scalar b x)) ^ 3 ≤
            (G.flow.base.metric b).inner x (gradientFun (G.flow.base.metric b) (G.flow.scalar b) x)
              (gradientFun (G.flow.base.metric b) (G.flow.scalar b) x) ∨
          C * (max q (G.flow.scalar b x)) ^ 2 ≤ |derivWithin (fun t => G.flow.scalar t x) (Iic b) b|)) →
    ∃ (H : ℕ → RetainedCoreHistory.{v}) (_ : ∀ i, InitialIdentification P g (H i).toHistory)
      (parameters : ℕ → CutoffParameters)
      (records : ∀ i j, GeometricCutoffRecord (H i).toHistory j (parameters i))
      (finish : ℕ → ℝ)
      (G : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).IncomingSlab
        ((H i).time (Fin.last (H i).eventCount)) (finish i)) (a b : ℕ → ℝ)
      (hstart : ∀ i, (H i).time (Fin.last (H i).eventCount) < a i)
      (hfinish : ∀ i, b i < finish i) (τ : ℕ → ℝ) (hτ : ∀ i, τ i ∈ Ioc (a i) (b i)),
      let A := fun i => (G i).closedPrefix (τ i) ((hstart i).trans (hτ i).1)
        ((hτ i).2.trans_lt (hfinish i));
      ∃ x : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).Carrier,
        (∀ i, (G i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
          (H i).initialMetric (Fin.last (H i).eventCount)) ∧
        (∀ i, (H i).time (Fin.last (H i).eventCount) = (H i).horizon) ∧
        (∀ i, finish i ≤ B) ∧
        (∀ i, amin < τ i ∧ τ i ≤ B ∧ (H i).horizon < τ i) ∧
        (∀ i, (parameters i).modelRadius = Dbig) ∧
        (∀ i, m ≤ (parameters i).modelOrder) ∧
        (∀ i j boundary, ((records i j).static boundary).hasCanonicalWindow) ∧
        (∀ i j boundary, (records i j).delta boundary ≤ δ₀) ∧
        (∀ i j, ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
          ∀ y : ((H i).stage j.castSucc).Carrier,
          q < ((H i).toHistory.event j).incoming.flow.scalar t y →
          |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2) ∧
        Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) ∧
        Tendsto (fun i => (A i).flow.scalar (τ i) (x i)) atTop atTop ∧
        (∀ i : ℕ, q + (i : ℝ) + 1 < (A i).flow.scalar (τ i) (x i) ∧
          ((∃ v : TangentSpace ThreeModel (x i), v ≠ 0 ∧
            C * (A i).flow.scalar (τ i) (x i) * Real.sqrt ((A i).flow.scalar (τ i) (x i)) *
                Real.sqrt (((A i).flow.base.metric (τ i)).inner (x i) v v) =
              |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (τ i)) (x i) v)|) ∨
            |derivWithin (fun t => (A i).flow.scalar t (x i)) (Iic (τ i)) (τ i)| =
              C * (A i).flow.scalar (τ i) (x i) ^ 2) ∧
          (∀ t ∈ Ico (a i) (τ i), ∀ y, q ≤ (A i).flow.scalar t y →
            ((A i).flow.base.metric t).inner y
              (gradientFun ((A i).flow.base.metric t) ((A i).flow.scalar t) y)
              (gradientFun ((A i).flow.base.metric t) ((A i).flow.scalar t) y) <
                C ^ 2 * (A i).flow.scalar t y ^ 3 ∧
            (∀ v : TangentSpace ThreeModel y,
              |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar t) y v)| ≤
                C * (A i).flow.scalar t y * Real.sqrt ((A i).flow.scalar t y) *
                  Real.sqrt (((A i).flow.base.metric t).inner y v v)) ∧
            |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| <
              C * (A i).flow.scalar t y ^ 2) ∧
          (∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (τ i), ∀ y,
            q ≤ (A i).flow.scalar t y →
            ((A i).flow.base.metric t).inner y
              (gradientFun ((A i).flow.base.metric t) ((A i).flow.scalar t) y)
              (gradientFun ((A i).flow.base.metric t) ((A i).flow.scalar t) y) <
                C ^ 2 * (A i).flow.scalar t y ^ 3 ∧
            |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| <
              C * (A i).flow.scalar t y ^ 2) ∧
          (∀ y, q ≤ (A i).flow.scalar (τ i) y →
            (∀ v : TangentSpace ThreeModel y,
              |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (τ i)) y v)| ≤
                C * (A i).flow.scalar (τ i) y * Real.sqrt ((A i).flow.scalar (τ i) y) *
                  Real.sqrt (((A i).flow.base.metric (τ i)).inner y v v)) ∧
            |derivWithin (fun v => (A i).flow.scalar v y) (Iic (τ i)) (τ i)| ≤
              C * (A i).flow.scalar (τ i) y ^ 2))) := by
  classical
  obtain ⟨amin, hamin, hfloor⟩ :=
    exists_pos_lt_scalar_derivative_contact_time_of_initialIdentification P g
  refine ⟨amin, hamin, ?_⟩
  intro C hC
  obtain ⟨q, hq, htime⟩ := hfloor C hC
  refine ⟨q, hq, ?_⟩
  intro hcounter
  have hchoice (i : ℕ) := hcounter (q + (i : ℝ) + 1)
    (by have hi := Nat.cast_nonneg (α := ℝ) i; linarith)
    (1 / ((i : ℝ) + 1)) (by positivity)
  choose H identification parameters records finish G a b hinit hhorizon hbounded hstart hab hfinish
    hmodelradius hmodelorder hwindows haccuracy hdelta hold hinitial hlow hpast hfail using hchoice
  have hcontact (i : ℕ) := (G i).exists_closedPrefix_first_scalar_derivative_contact
    (hstart i) (hab i) (hfinish i) hC hq
    (show q ≤ q + (i : ℝ) + 1 by have hi := Nat.cast_nonneg (α := ℝ) i; linarith)
    (hinitial i) (hlow i) (hpast i) (hfail i)
  choose τ hτ x hhigh hcontact hbefore hpast hat using hcontact
  refine ⟨H, identification, parameters, records, finish, G, a, b, hstart, hfinish, τ, hτ,
    x, hinit, hhorizon, hbounded, ?_, hmodelradius, hmodelorder, hwindows, hdelta, hold, ?_, ?_, ?_⟩
  · intro i
    have hregular : τ i ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (finish i) :=
      ⟨(hstart i).trans (hτ i).1, (hτ i).2.trans_lt (hfinish i)⟩
    have hqQ : q ≤ q + (i : ℝ) + 1 := by
      have hi := Nat.cast_nonneg (α := ℝ) i
      linarith
    have ht := htime (H i).toHistory (identification i) (fun j => (records i j).singular)
      (Fin.last (H i).eventCount) (finish i) (G i) (hinit i) (τ i) hregular (x i)
      (hqQ.trans (hhigh i).le) (hcontact i)
    exact ⟨ht, ((hτ i).2.trans (hfinish i).le).trans (hbounded i),
      by rw [← hhorizon i]; exact hregular.1⟩
  · exact squeeze_zero (fun i => (parameters i).modelAccuracy_pos.le) haccuracy
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · have hQ : Tendsto (fun i : ℕ => q + (i : ℝ) + 1) atTop atTop := by
      have hnat := tendsto_atTop_add_const_right atTop (q + 1)
        (tendsto_natCast_atTop_atTop (R := ℝ))
      convert hnat using 1
      ext i
      ring
    exact tendsto_atTop_mono (fun i => (hhigh i).le) hQ
  · exact fun i => ⟨hhigh i, hcontact i, hbefore i, hpast i, hat i⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
