import FailureOfSemipositiveMetricExtension.FourthPowerLineBundle

/-! Actual L⁴-valued alternating tangent two-forms for the Cao interface. The
coefficient in an independent coordinate chart and line frame includes the
proved canonical Jacobian, with its correct transition direction. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

abbrev CentralData := FixedFiberBundle.AdjointSectionData 0 4

/-- An intrinsic alternating form valued in the genuine fourth-power fibre. -/
def centralForm (s : CentralData) : CaoExtensionInterface.CentralForm family fourthPowerLine :=
  fun p => let d := powerCore.indexAt (FixedFiber.inclusion 0 p)
    s.coefficient d p • FixedFiber.tangentCoordinateForm 0 d.1 d.2.1 p

/-- Its genuine line-trivialization coordinate is the existing adjoint
coefficient times the actual tangent coordinate volume. -/
theorem centralForm_localTriv (s : CentralData) (c : PowerIndex) (p : Fiber 0)
    (hc : p ∈ FixedFiberBundle.divisionPatch 0 c)
    (v : Fin 2 → TangentSpace 𝓘(ℂ,FixedFiber.Coord) p) :
    (powerCore.localTriv c ⟨FixedFiber.inclusion 0 p,centralForm s p v⟩).2 =
      s.coefficient c p * FixedFiber.tangentCoordinateForm 0 c.1 c.2.1 p v := by
  let d := powerCore.indexAt (FixedFiber.inclusion 0 p)
  have hd : p ∈ FixedFiberBundle.divisionPatch 0 d := powerCore.mem_baseSet_at _
  rw [VectorBundleCore.localTriv_apply]
  change powerGain d c (FixedFiber.inclusion 0 p) *
    (s.coefficient d p * FixedFiber.tangentCoordinateForm 0 d.1 d.2.1 p v) = _
  have hf : FixedFiber.tangentCoordinateForm 0 d.1 d.2.1 p =
      FixedFiber.canonicalGain 0 (FixedFiberBundle.divisionChart d)
        (FixedFiberBundle.divisionChart c) p • FixedFiber.tangentCoordinateForm 0 c.1 c.2.1 p :=
    FixedFiber.tangentCoordinateForm_canonicalGain 0
      (FixedFiberBundle.divisionChart d) (FixedFiberBundle.divisionChart c) p hd.1 hc.1
  rw [hf]
  have hs := s.compatible d c p hd hc
  change (FixedFiber.canonicalGain 0 (FixedFiberBundle.divisionChart d)
    (FixedFiberBundle.divisionChart c) p * powerGain d c (FixedFiber.inclusion 0 p)) *
      s.coefficient d p = s.coefficient c p at hs
  rw [← hs]
  simp only [AlternatingMap.smul_apply,smul_eq_mul]
  ring

/-- Exact scalar coefficient, in independently selected coordinate and line
frames. No equality of their chart indices is assumed. -/
def centralCoefficient (s : CentralData) (a : ChartIndex) (d : PowerIndex) (p : Fiber 0) : ℂ :=
  FixedFiber.canonicalGain 0 (FixedFiberBundle.divisionChart d) a p * s.coefficient d p

theorem centralCoefficient_analytic (s : CentralData) (a : ChartIndex) (d : PowerIndex) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (centralCoefficient s a d)
      (CaoExtensionInterface.centralPatch family fourthPowerLine a d) := by
  have hk := (FixedFiber.chartJacobian_contMDiffOn 0 a.1 d.1 a.2 d.2.1).mono
    (show (CaoExtensionInterface.centralPatch family fourthPowerLine a d : Set (Fiber 0)) ⊆
      FixedFiber.source 0 a.1 a.2 ∩ FixedFiber.source 0 d.1 d.2.1 from
        fun p hp => ⟨hp.1,hp.2.1⟩)
  have hs := (s.analytic d).mono
    (show (CaoExtensionInterface.centralPatch family fourthPowerLine a d : Set (Fiber 0)) ⊆
      FixedFiberBundle.divisionPatch 0 d from fun p hp => hp.2)
  exact hk.smul hs

/-- A genuine central adjoint section in the generic interface, built from the
already constructed actual bundle section. -/
def centralSection (s : CentralData) :
    CaoExtensionInterface.CentralAdjointSection family fourthPowerLine where
  form := centralForm s
  coefficient := centralCoefficient s
  analytic := centralCoefficient_analytic s
  represents a d p hp v := by
    change (powerCore.localTriv d ⟨FixedFiber.inclusion 0 p,centralForm s p v⟩).2 =
      centralCoefficient s a d p * FixedFiber.tangentCoordinateForm 0 a.1 a.2 p v
    rw [centralForm_localTriv s d p hp.2]
    have hf : FixedFiber.tangentCoordinateForm 0 d.1 d.2.1 p =
        FixedFiber.canonicalGain 0 (FixedFiberBundle.divisionChart d) a p •
          FixedFiber.tangentCoordinateForm 0 a.1 a.2 p :=
      FixedFiber.tangentCoordinateForm_canonicalGain 0
        (FixedFiberBundle.divisionChart d) a p hp.2.1 hp.1
    rw [hf]
    simp only [AlternatingMap.smul_apply,smul_eq_mul,centralCoefficient]
    ring

@[simp] theorem centralSection_diagonal (s : CentralData) (d : PowerIndex) (p : Fiber 0) :
    (centralSection s).coefficient (GlobalAdjoint.chart d) d p = s.coefficient d p := by
  change FixedFiber.canonicalGain 0 (FixedFiberBundle.divisionChart d)
    (FixedFiberBundle.divisionChart d) p * _ = _
  rw [FixedFiber.canonicalGain_self,one_mul]

/-- The actual distinguished σ, including its canonical unit correction, as a
true L⁴-valued alternating tangent two-form. -/
def sigmaCentralSection := centralSection FixedFiberBundle.sigmaAdjointData

@[simp] theorem sigmaCentralSection_coefficient (a : ChartIndex) (d : PowerIndex) (p : Fiber 0) :
    sigmaCentralSection.coefficient a d p =
      FixedFiber.canonicalGain 0 (FixedFiberBundle.divisionChart d) a p *
        FixedFiberBundle.sigmaAdjointCoefficient d p := rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
