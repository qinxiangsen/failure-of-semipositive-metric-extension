import FailureOfSemipositiveMetricExtension.CentralNormCover
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Actual finite Borel measures obtained from the proved coordinate integrals.
Their finite covering sum is constructed explicitly. Identification with the
intrinsic canonical norm measure still requires the overlap change-of-variables
bridge; no such identification is assumed in this file. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set MeasureTheory Topology
open scoped ENNReal

local instance centralBorel : MeasurableSpace (Fiber 0) := borel (Fiber 0)
local instance centralBorelSpace : BorelSpace (Fiber 0) := ⟨rfl⟩

def CentralNormPatch.coordinateMeasure (P : CentralNormPatch) : Measure FixedFiber.Coord :=
  (volume.restrict (Metric.closedBall P.center P.radius)).withDensity
    (fun q => sigmaAdjointExtendedDensity P.frame (FixedFiber.param 0 P.frame.1 P.frame.2.1 q))

instance CentralNormPatch.coordinateMeasure_finite (P : CentralNormPatch) :
    IsFiniteMeasure P.coordinateMeasure :=
  isFiniteMeasure_withDensity P.normIntegral_lt_top.ne

theorem CentralNormPatch.coordinateMeasure_mass (P : CentralNormPatch) :
    P.coordinateMeasure univ = P.normIntegral := by
  rw [CentralNormPatch.coordinateMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rfl

/-- This is a genuine Borel pushforward of the density on a closed coordinate
ball; the next lemma verifies the map is actually a.e. measurable. -/
def CentralNormPatch.pushforwardMeasure (P : CentralNormPatch) : Measure (Fiber 0) :=
  P.coordinateMeasure.map (FixedFiber.param 0 P.frame.1 P.frame.2.1)

theorem CentralNormPatch.param_aemeasurable (P : CentralNormPatch) :
    AEMeasurable (FixedFiber.param 0 P.frame.1 P.frame.2.1) P.coordinateMeasure := by
  have h := ((FixedFiber.param_contMDiffOn 0 P.frame.1 P.frame.2.1 0).continuousOn.mono
    P.closed_subdomain).aemeasurable (μ := volume) measurableSet_closedBall
  exact h.mono_ac (withDensity_absolutelyContinuous _ _)

instance CentralNormPatch.pushforwardMeasure_finite (P : CentralNormPatch) :
    IsFiniteMeasure P.pushforwardMeasure := Measure.isFiniteMeasure_map _ _

theorem CentralNormPatch.pushforwardMeasure_mass (P : CentralNormPatch) :
    P.pushforwardMeasure univ = P.normIntegral := by
  rw [CentralNormPatch.pushforwardMeasure,Measure.map_apply_of_aemeasurable P.param_aemeasurable
    MeasurableSet.univ,preimage_univ,P.coordinateMeasure_mass]

def centralCoverMeasure (S : Finset CentralNormPatch) : Measure (Fiber 0) :=
  ∑ P ∈ S, P.pushforwardMeasure

instance centralCoverMeasure_finite (S : Finset CentralNormPatch) : IsFiniteMeasure (centralCoverMeasure S) := by
  unfold centralCoverMeasure
  infer_instance

theorem centralCoverMeasure_mass (S : Finset CentralNormPatch) :
    centralCoverMeasure S univ = ∑ P ∈ S, P.normIntegral := by
  simp [centralCoverMeasure,Measure.sum_apply,CentralNormPatch.pushforwardMeasure_mass]

theorem exists_finite_cover_measure :
    ∃ S : Finset CentralNormPatch, (∀ p : Fiber 0, ∃ P ∈ S, p ∈ P.openSet) ∧
      centralCoverMeasure S univ < ⊤ := by
  obtain ⟨S,hS,hI⟩ := finite_central_norm_cover
  exact ⟨S,hS,by rwa [centralCoverMeasure_mass]⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
