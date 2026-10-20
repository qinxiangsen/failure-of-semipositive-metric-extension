import FailureOfSemipositiveMetricExtension.CentralCanonicalNorm

/-! Gluing for any genuine compatible canonical density with finite coordinate
integrals. The subsequent actual-metric instantiations prove both input fields;
this structure is not an external theorem or a postulated paper conclusion. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set MeasureTheory Topology
open ComplexSurfaceJacobian
open scoped ENNReal
attribute [local instance] centralBorel centralBorelSpace

structure CanonicalNormDensity where
  density : DivisionIndex → Fiber 0 → ℝ≥0∞
  transition : ∀ d c p, p ∈ divisionPatch 0 d → p ∈ divisionPatch 0 c →
    density c p = ENNReal.ofReal
      (Complex.normSq (FixedFiber.canonicalGain 0 (divisionChart d) (divisionChart c) p)) * density d p
  finite_on_patch : ∀ P : CentralNormPatch,
    (∫⁻ q in Metric.closedBall P.center P.radius,
      density P.frame (FixedFiber.param 0 P.frame.1 P.frame.2.1 q)) < ⊤

namespace CanonicalNormDensity
variable (ρ : CanonicalNormDensity)

theorem forward_jacobian (d c : DivisionIndex) (q : FixedFiber.Coord)
    (hd : FixedFiber.param 0 d.1 d.2.1 q ∈ divisionPatch 0 d)
    (hc : FixedFiber.param 0 d.1 d.2.1 q ∈ divisionPatch 0 c) :
    ENNReal.ofReal (Complex.normSq (jacobian (FixedFiber.change 0 d.1 c.1 d.2.1 c.2.1) q)) *
      ρ.density c (FixedFiber.param 0 d.1 d.2.1 q) =
        ρ.density d (FixedFiber.param 0 d.1 d.2.1 q) := by
  let p := FixedFiber.param 0 d.1 d.2.1 q
  have hq : q ∈ FixedFiber.changeDomain 0 d.1 c.1 d.2.1 c.2.1 := by
    simpa only [p,FixedFiber.coordinates_param] using
      FixedFiber.coordinates_mem_changeDomain 0 d.1 c.1 d.2.1 c.2.1 p hd.1 hc.1
  have hi := FixedFiber.change_jacobian_inverse 0 d.1 c.1 d.2.1 c.2.1 q hq
  have hg : FixedFiber.canonicalGain 0 (divisionChart d) (divisionChart c) p =
      jacobian (FixedFiber.change 0 c.1 d.1 c.2.1 d.2.1)
        (FixedFiber.change 0 d.1 c.1 d.2.1 c.2.1 q) := rfl
  rw [ρ.transition d c _ hd hc,← mul_assoc]
  change (_ * ENNReal.ofReal (Complex.normSq (FixedFiber.canonicalGain 0 (divisionChart d) (divisionChart c) p))) * _ = _
  rw [hg,← ENNReal.ofReal_mul (Complex.normSq_nonneg _),← Complex.normSq_mul,
    mul_comm (jacobian (FixedFiber.change 0 d.1 c.1 d.2.1 c.2.1) q),hi]
  simp

theorem lintegral_change (d c : DivisionIndex) (S : Set FixedFiber.Coord)
    (hS : MeasurableSet S)
    (hd : MapsTo (FixedFiber.param 0 d.1 d.2.1) S (divisionPatch 0 d))
    (hc : MapsTo (FixedFiber.param 0 d.1 d.2.1) S (divisionPatch 0 c)) :
    (∫⁻ q in FixedFiber.change 0 d.1 c.1 d.2.1 c.2.1 '' S,
      ρ.density c (FixedFiber.param 0 c.1 c.2.1 q)) =
    ∫⁻ q in S, ρ.density d (FixedFiber.param 0 d.1 d.2.1 q) := by
  have hdom : S ⊆ FixedFiber.changeDomain 0 d.1 c.1 d.2.1 c.2.1 := by
    intro q hq
    simpa only [FixedFiber.coordinates_param] using
      FixedFiber.coordinates_mem_changeDomain 0 d.1 c.1 d.2.1 c.2.1
        (FixedFiber.param 0 d.1 d.2.1 q) (hd hq).1 (hc hq).1
  rw [lintegral_image_complex_jacobian hS
    (fun q hq => FixedFiber.change_differentiableAt _ _ _ _ _ q (hdom hq))
    ((fixedFiber_change_injOn _ _ _ _ _).mono hdom)]
  apply setLIntegral_congr_fun hS
  filter_upwards [] with q hq
  change _ * ρ.density c
    (FixedFiber.param 0 c.1 c.2.1
      (FixedFiber.coordinates 0 c.1 c.2.1 (FixedFiber.param 0 d.1 d.2.1 q))) = _
  rw [FixedFiber.param_coordinates _ _ _ _ (hc hq).1]
  exact ρ.forward_jacobian d c q (hd hq) (hc hq)

def coordinateMeasure (P : CentralNormPatch) : Measure FixedFiber.Coord :=
  (volume.restrict (Metric.closedBall P.center P.radius)).withDensity
    (fun q => ρ.density P.frame (FixedFiber.param 0 P.frame.1 P.frame.2.1 q))

instance coordinateMeasure_finite (P : CentralNormPatch) : IsFiniteMeasure (ρ.coordinateMeasure P) :=
  isFiniteMeasure_withDensity (ρ.finite_on_patch P).ne

def patchMeasure (P : CentralNormPatch) : Measure (Fiber 0) :=
  (ρ.coordinateMeasure P).map (FixedFiber.param 0 P.frame.1 P.frame.2.1)

theorem param_aemeasurable (P : CentralNormPatch) :
    AEMeasurable (FixedFiber.param 0 P.frame.1 P.frame.2.1) (ρ.coordinateMeasure P) := by
  have h := ((FixedFiber.param_contMDiffOn 0 P.frame.1 P.frame.2.1 0).continuousOn.mono
    P.closed_subdomain).aemeasurable (μ := volume) measurableSet_closedBall
  exact h.mono_ac (withDensity_absolutelyContinuous _ _)

instance patchMeasure_finite (P : CentralNormPatch) : IsFiniteMeasure (ρ.patchMeasure P) :=
  Measure.isFiniteMeasure_map _ _

theorem patchMeasure_apply (P : CentralNormPatch) (S : Set (Fiber 0))
    (hS : MeasurableSet S) (hsub : S ⊆ P.openSet) :
    ρ.patchMeasure P S = ∫⁻ q in FixedFiber.coordinates 0 P.frame.1 P.frame.2.1 '' S,
      ρ.density P.frame (FixedFiber.param 0 P.frame.1 P.frame.2.1 q) := by
  rw [patchMeasure,Measure.map_apply_of_aemeasurable (ρ.param_aemeasurable P) hS,
    coordinateMeasure,withDensity_apply',Measure.restrict_restrict' measurableSet_closedBall,
    P.preimage_inter_closedBall S hsub]

theorem measures_agree (P Q : CentralNormPatch) (S : Set (Fiber 0)) (hS : MeasurableSet S)
    (hP : S ⊆ P.openSet) (hQ : S ⊆ Q.openSet) : ρ.patchMeasure P S = ρ.patchMeasure Q S := by
  rw [ρ.patchMeasure_apply P S hS hP,ρ.patchMeasure_apply Q S hS hQ]
  have hd : S ⊆ FixedFiber.source 0 P.frame.1 P.frame.2.1 := fun p hp => (hP hp).1
  have h := ρ.lintegral_change P.frame Q.frame
    (FixedFiber.coordinates 0 P.frame.1 P.frame.2.1 '' S)
    (coordinates_image_measurable P.frame S hS hd)
    (by rintro q ⟨p,hp,rfl⟩; rw [FixedFiber.param_coordinates _ _ _ p (hd hp)]; exact P.subset_patch (hP hp))
    (by rintro q ⟨p,hp,rfl⟩; rw [FixedFiber.param_coordinates _ _ _ p (hd hp)]; exact Q.subset_patch (hQ hp))
  rw [coordinates_image_change P.frame Q.frame S hd] at h
  exact h.symm

theorem restrict_measures_agree (P Q : CentralNormPatch) :
    (ρ.patchMeasure P).restrict (P.openSet ∩ Q.openSet) =
      (ρ.patchMeasure Q).restrict (P.openSet ∩ Q.openSet) := by
  ext S hS
  rw [Measure.restrict_apply hS,Measure.restrict_apply hS]
  exact ρ.measures_agree P Q _ (hS.inter (P.isOpen.measurableSet.inter Q.isOpen.measurableSet))
    (fun p hp => hp.2.1) (fun p hp => hp.2.2)

def globalMeasure : Measure (Fiber 0) :=
  MeasureGluing.finiteGlue (fun i => (centralNormChosenCover.patch i).openSet)
    (fun i => ρ.patchMeasure (centralNormChosenCover.patch i))

instance globalMeasure_finite : IsFiniteMeasure ρ.globalMeasure := by
  unfold globalMeasure
  infer_instance

theorem globalMeasure_restrict (P : CentralNormPatch) :
    ρ.globalMeasure.restrict P.openSet = (ρ.patchMeasure P).restrict P.openSet :=
  MeasureGluing.finiteGlue_restrict_other _ _
    (fun i => (centralNormChosenCover.patch i).isOpen.measurableSet)
    centralNormChosenCover.covers _ P.isOpen.measurableSet _
    (fun i => ρ.restrict_measures_agree (centralNormChosenCover.patch i) P)

theorem globalMeasure_local_density (P : CentralNormPatch) (S : Set (Fiber 0))
    (hS : MeasurableSet S) (hsub : S ⊆ P.openSet) :
    ρ.globalMeasure S = ∫⁻ q in FixedFiber.coordinates 0 P.frame.1 P.frame.2.1 '' S,
      ρ.density P.frame (FixedFiber.param 0 P.frame.1 P.frame.2.1 q) := by
  have h := congrArg (fun μ : Measure (Fiber 0) => μ S) (ρ.globalMeasure_restrict P)
  change ρ.globalMeasure.restrict P.openSet S = (ρ.patchMeasure P).restrict P.openSet S at h
  rw [Measure.restrict_apply hS,Measure.restrict_apply hS,inter_eq_left.mpr hsub] at h
  exact h.trans (ρ.patchMeasure_apply P S hS hsub)

theorem globalMeasure_unique (ν : Measure (Fiber 0))
    (hν : ∀ P : CentralNormPatch, ν.restrict P.openSet = (ρ.patchMeasure P).restrict P.openSet) :
    ν = ρ.globalMeasure := by
  apply Measure.ext_of_iUnion_eq_univ centralNormChosenCover.covers
  intro i
  rw [hν,ρ.globalMeasure_restrict]

theorem global_mass_finite : ρ.globalMeasure univ < ⊤ := measure_lt_top _ _

end CanonicalNormDensity
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
