import FailureOfSemipositiveMetricExtension.MetricPlurisubharmonicity

/-! Singular metric weights on arbitrary actual open neighbourhoods in the
constructed total space, their actual central restriction and exact extension
comparison predicates. No existence or nonextension assertion is assumed. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff

/-- Compatible extended weights on an actual open subset of the actual total space. -/
structure SingularWeightOn (U : Opens GlobalIncidence.Total) (a : ℤ) (b : Fin 4 → ℤ) where
  weight : Index → GlobalIncidence.Total → WithBot ℝ
  compatible : ∀ i j p, p ∈ U → p ∈ baseSet i ∩ baseSet j →
    weight j p = weight i p + (Real.log (Complex.normSq (gain a b i j p)) : ℝ)

def globalWeightChartDomain (U : Opens GlobalIncidence.Total) (i : Index)
    (r : Fin 4) (e : Fin 2) : Set GlobalIncidence.ChartCoord :=
  GlobalIncidence.chartDomain r e ∩ GlobalIncidence.chartParam r e ⁻¹' (baseSet i ∩ U)

theorem globalWeightChartDomain_isOpen (U : Opens GlobalIncidence.Total) (i : Index)
    (r : Fin 4) (e : Fin 2) : IsOpen (globalWeightChartDomain U i r e) :=
  (GlobalIncidence.homeomorphChart r e).isOpen_inter_preimage_symm ((baseSet_isOpen i).inter U.2)

def SingularWeightOn.HasPlurisubharmonicWeights {U : Opens GlobalIncidence.Total}
    {a : ℤ} {b : Fin 4 → ℤ} (h : SingularWeightOn U a b) : Prop :=
  ∀ i r e, FailureOfSemipositiveMetricExtension.PlurisubharmonicOn
    (fun q => h.weight i (GlobalIncidence.chartParam r e q)) (globalWeightChartDomain U i r e)

/-- The whole actual central fibre is contained in the metric's domain. -/
def ContainsCentralFiber (U : Opens GlobalIncidence.Total) : Prop :=
  ∀ p : GlobalIncidence.Fiber 0, GlobalIncidence.FixedFiber.inclusion 0 p ∈ U

def SingularWeightOn.centralRestriction {U : Opens GlobalIncidence.Total}
    {a : ℤ} {b : Fin 4 → ℤ} (h : SingularWeightOn U a b) (hU : ContainsCentralFiber U) :
    GlobalIncidence.FixedFiberBundle.SingularHermitianWeight 0 a b where
  weight i p := h.weight i (GlobalIncidence.FixedFiber.inclusion 0 p)
  compatible i j p hp := h.compatible i j _ (hU p) hp

/-- The actual restricted weights have at least one finite point in a valid frame.
No regularity or well-defined restriction is inferred from this predicate alone. -/
def SingularWeightOn.centralRestrictionNotIdenticallyBot {U : Opens GlobalIncidence.Total}
    {a : ℤ} {b : Fin 4 → ℤ} (h : SingularWeightOn U a b) : Prop :=
  ∃ (p : GlobalIncidence.Fiber 0) (i : Index),
    p ∈ GlobalIncidence.FixedFiberBundle.baseSet 0 i ∧
      h.weight i (GlobalIncidence.FixedFiber.inclusion 0 p) ≠ ⊥

/-- The precise one-sided inequality in Theorem A, for compatible actual frames. -/
def SingularWeightOn.centralDominatesH0 {U : Opens GlobalIncidence.Total}
    (h : SingularWeightOn U (-2) (fun _ => 1)) : Prop :=
  ∃ C : ℝ, ∀ (i : Index) (p : GlobalIncidence.Fiber 0),
    p ∈ GlobalIncidence.FixedFiberBundle.baseSet 0 i →
      GlobalIncidence.FixedFiberBundle.centralH0.weight i p + ((-C : ℝ) : WithBot ℝ) ≤
        h.weight i (GlobalIncidence.FixedFiber.inclusion 0 p)

def SingularWeightOn.centralExactH0 {U : Opens GlobalIncidence.Total}
    (h : SingularWeightOn U (-2) (fun _ => 1)) : Prop :=
  ∀ (i : Index) (p : GlobalIncidence.Fiber 0),
    p ∈ GlobalIncidence.FixedFiberBundle.baseSet 0 i →
      h.weight i (GlobalIncidence.FixedFiber.inclusion 0 p) =
        GlobalIncidence.FixedFiberBundle.centralH0.weight i p

theorem SingularWeightOn.centralExactH0_dominates {U : Opens GlobalIncidence.Total}
    (h : SingularWeightOn U (-2) (fun _ => 1)) (he : h.centralExactH0) :
    h.centralDominatesH0 := by
  refine ⟨0,?_⟩
  intro i p hp
  rw [he i p hp]
  simp

end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
