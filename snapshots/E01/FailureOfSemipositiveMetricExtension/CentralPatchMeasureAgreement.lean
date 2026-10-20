import FailureOfSemipositiveMetricExtension.CentralNormMeasure
import FailureOfSemipositiveMetricExtension.CentralDensityChangeOfVariables

/-! Agreement of the actual finite chart measures on chart overlaps.  This is
the measure-theoretic gluing condition for the intrinsic canonical norm. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set MeasureTheory Topology
open scoped ENNReal

attribute [local instance] centralBorel centralBorelSpace

theorem coordinates_image_measurable (d : DivisionIndex) (S : Set (Fiber 0))
    (hS : MeasurableSet S) (hsub : S ⊆ FixedFiber.source 0 d.1 d.2.1) :
    MeasurableSet (FixedFiber.coordinates 0 d.1 d.2.1 '' S) := by
  let e := FixedFiber.chart 0 d.1 d.2.1
  have h := e.isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image.mpr
    (hS.preimage (measurable_subtype_coe : Measurable (fun p : e.source => (p : Fiber 0))))
  have he : e.source.restrict e '' ((fun p : e.source => (p : Fiber 0)) ⁻¹' S) =
      FixedFiber.coordinates 0 d.1 d.2.1 '' S := by
    ext q
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨p,hp,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      exact ⟨⟨p,hsub hp⟩,hp,rfl⟩
  rwa [he] at h

theorem CentralNormPatch.preimage_inter_closedBall (P : CentralNormPatch) (S : Set (Fiber 0))
    (hsub : S ⊆ P.openSet) :
    FixedFiber.param 0 P.frame.1 P.frame.2.1 ⁻¹' S ∩ Metric.closedBall P.center P.radius =
      FixedFiber.coordinates 0 P.frame.1 P.frame.2.1 '' S := by
  ext q
  constructor
  · rintro ⟨hq,_⟩
    exact ⟨FixedFiber.param 0 P.frame.1 P.frame.2.1 q,hq,FixedFiber.coordinates_param _ _ _ q⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨by change FixedFiber.param 0 P.frame.1 P.frame.2.1 (FixedFiber.coordinates 0 P.frame.1 P.frame.2.1 p) ∈ S; rwa [FixedFiber.param_coordinates _ _ _ p (hsub hp).1],
      Metric.ball_subset_closedBall (hsub hp).2⟩

theorem CentralNormPatch.pushforwardMeasure_apply (P : CentralNormPatch) (S : Set (Fiber 0))
    (hS : MeasurableSet S) (hsub : S ⊆ P.openSet) :
    P.pushforwardMeasure S = ∫⁻ q in FixedFiber.coordinates 0 P.frame.1 P.frame.2.1 '' S,
      sigmaAdjointExtendedDensity P.frame (FixedFiber.param 0 P.frame.1 P.frame.2.1 q) := by
  rw [CentralNormPatch.pushforwardMeasure,Measure.map_apply_of_aemeasurable P.param_aemeasurable hS,
    CentralNormPatch.coordinateMeasure,withDensity_apply',Measure.restrict_restrict' measurableSet_closedBall,
    P.preimage_inter_closedBall S hsub]

theorem coordinates_image_change (d c : DivisionIndex) (S : Set (Fiber 0))
    (hsub : S ⊆ FixedFiber.source 0 d.1 d.2.1) :
    FixedFiber.change 0 d.1 c.1 d.2.1 c.2.1 ''
        (FixedFiber.coordinates 0 d.1 d.2.1 '' S) =
      FixedFiber.coordinates 0 c.1 c.2.1 '' S := by
  rw [← image_comp]
  apply image_congr
  intro p hp
  change FixedFiber.coordinates 0 c.1 c.2.1
    (FixedFiber.param 0 d.1 d.2.1 (FixedFiber.coordinates 0 d.1 d.2.1 p)) = _
  rw [FixedFiber.param_coordinates _ _ _ p (hsub hp)]

theorem CentralNormPatch.measures_agree_on_overlap (P Q : CentralNormPatch)
    (S : Set (Fiber 0)) (hS : MeasurableSet S) (hP : S ⊆ P.openSet) (hQ : S ⊆ Q.openSet) :
    P.pushforwardMeasure S = Q.pushforwardMeasure S := by
  rw [P.pushforwardMeasure_apply S hS hP,Q.pushforwardMeasure_apply S hS hQ]
  have hd : S ⊆ FixedFiber.source 0 P.frame.1 P.frame.2.1 := fun p hp => (hP hp).1
  have h := sigma_density_lintegral_change P.frame Q.frame
    (FixedFiber.coordinates 0 P.frame.1 P.frame.2.1 '' S)
    (coordinates_image_measurable P.frame S hS hd)
    (by rintro q ⟨p,hp,rfl⟩; rw [FixedFiber.param_coordinates _ _ _ p (hd hp)]; exact P.subset_patch (hP hp))
    (by rintro q ⟨p,hp,rfl⟩; rw [FixedFiber.param_coordinates _ _ _ p (hd hp)]; exact Q.subset_patch (hQ hp))
  rw [coordinates_image_change P.frame Q.frame S hd] at h
  exact h.symm

theorem CentralNormPatch.restrict_measures_agree (P Q : CentralNormPatch) :
    P.pushforwardMeasure.restrict (P.openSet ∩ Q.openSet) =
      Q.pushforwardMeasure.restrict (P.openSet ∩ Q.openSet) := by
  ext S hS
  rw [Measure.restrict_apply hS,Measure.restrict_apply hS]
  exact P.measures_agree_on_overlap Q _ (hS.inter (P.isOpen.measurableSet.inter Q.isOpen.measurableSet))
    (fun p hp => hp.2.1) (fun p hp => hp.2.2)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
